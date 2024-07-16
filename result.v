module ppu_core_ops (
	clk_i,
	rst_i,
	p1_i,
	p2_i,
	p3_i,
	op_i,
	op_o,
	stall_i,
	float_fir_i,
	posit_fir_o,
	pout_o,
	fixed_o
);
	parameter N = -1;
	parameter ES = -1;
	parameter FSIZE = -1;
	input clk_i;
	input rst_i;
	localparam ppu_pkg_N = 16;
	input wire [15:0] p1_i;
	input wire [15:0] p2_i;
	input wire [15:0] p3_i;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	output wire [2:0] op_o;
	input stall_i;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_RECIPROCATE_MANT_SIZE = 28;
	localparam ppu_pkg_RMS = ppu_pkg_RECIPROCATE_MANT_SIZE;
	localparam ppu_pkg_MANT_DIV_RESULT_SIZE = 42;
	localparam ppu_pkg_FRAC_FULL_SIZE = 40;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input [47:0] float_fir_i;
	output wire [21:0] posit_fir_o;
	output wire [15:0] pout_o;
	output wire [63:0] fixed_o;
	localparam STAGES = 4;
	wire [2:0] op [3:0];
	wire [15:0] p1 [3:0];
	wire [15:0] p2 [3:0];
	wire [15:0] p3 [3:0];
	wire [21:0] fir1 [3:0];
	wire [21:0] fir2 [3:0];
	wire [21:0] fir3 [3:0];
	wire [16:0] p_special [3:0];
	wire [63:0] fixed [3:0];
	wire [48:0] ops_result [3:0];
	extraction #(.N(N)) extraction_i(
		.p1_i(p1[0]),
		.p2_i(p2[0]),
		.p3_i(p3[0]),
		.op_i(op[0]),
		.op_o(op[1]),
		.fir1_o(fir1[1]),
		.fir2_o(fir2[1]),
		.fir3_o(fir3[1]),
		.p_special_o(p_special[1])
	);
	fir_ops #(.N(N)) fir_ops_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.op_i(op[2]),
		.fir1_i(fir1[2]),
		.fir2_i(fir2[2]),
		.fir3_i(fir3[2]),
		.ops_result_o(ops_result[2]),
		.fixed_o(fixed[2])
	);
	normalization #(
		.N(N),
		.ES(ES),
		.FIR_TOTAL_SIZE(48),
		.TE_BITS(ppu_pkg_TE_BITS),
		.FRAC_FULL_SIZE(ppu_pkg_FRAC_FULL_SIZE)
	) normalization_inst(
		.ops_result_i(ops_result[3]),
		.p_special_i(p_special[3]),
		.posit_o(pout_o)
	);
	localparam _PIPE_DEPTH = 0;
	pipeline #(
		.PIPELINE_DEPTH(_PIPE_DEPTH),
		.DATA_WIDTH(51)
	) pipeline_st0(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.data_in({op_i, p1_i, p2_i, p3_i}),
		.data_out({op[0], p1[0], p2[0], p3[0]})
	);
	pipeline #(
		.PIPELINE_DEPTH(_PIPE_DEPTH),
		.DATA_WIDTH(86)
	) pipeline_st1(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.data_in({op[1], fir1[1], fir2[1], fir3[1], p_special[1]}),
		.data_out({op[2], fir1[2], fir2[2], fir3[2], p_special[2]})
	);
	function automatic [2:0] sv2v_cast_F65AF;
		input reg [2:0] inp;
		sv2v_cast_F65AF = inp;
	endfunction
	pipeline #(
		.PIPELINE_DEPTH(0),
		.DATA_WIDTH(130)
	) pipeline_st2(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.data_in({fixed[2], (op_i == sv2v_cast_F65AF(6) ? float_fir_i : ops_result[2]), p_special[2]}),
		.data_out({fixed[3], ops_result[3], p_special[3]})
	);
	assign fixed_o = fixed[3];
	assign posit_fir_o = fir2[2];
endmodule
module accumulator (
	clk_i,
	rst_i,
	start_i,
	init_value_i,
	fixed_i,
	fixed_o
);
	parameter FIXED_SIZE = -1;
	input wire clk_i;
	input wire rst_i;
	input wire start_i;
	input wire signed [FIXED_SIZE - 1:0] init_value_i;
	input wire signed [FIXED_SIZE - 1:0] fixed_i;
	output wire signed [FIXED_SIZE - 1:0] fixed_o;
	reg signed [FIXED_SIZE - 1:0] fixed_o_st1;
	always @(posedge clk_i)
		if (rst_i)
			fixed_o_st1 <= 'b0;
		else
			fixed_o_st1 <= fixed_o;
	assign fixed_o = fixed_i + (start_i == 1'b1 ? init_value_i : fixed_o_st1);
endmodule
module input_conditioning (
	p1_i,
	p2_i,
	p3_i,
	op_i,
	p1_o,
	p2_o,
	p3_o,
	p_special_o
);
	parameter N = -1;
	localparam ppu_pkg_N = 16;
	input wire [15:0] p1_i;
	input wire [15:0] p2_i;
	input wire [15:0] p3_i;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	output wire [15:0] p1_o;
	output wire [15:0] p2_o;
	output wire [15:0] p3_o;
	output wire [16:0] p_special_o;
	assign p3_o = p3_i;
	wire [15:0] _p1;
	wire [15:0] _p2;
	assign _p1 = p1_i;
	function [15:0] ppu_pkg_c2;
		input [15:0] a;
		ppu_pkg_c2 = ~a + 1'b1;
	endfunction
	function automatic [2:0] sv2v_cast_F65AF;
		input reg [2:0] inp;
		sv2v_cast_F65AF = inp;
	endfunction
	assign _p2 = (op_i == sv2v_cast_F65AF(1) ? ppu_pkg_c2(p2_i) : p2_i);
	assign {p1_o, p2_o} = {_p1, _p2};
	wire is_special_or_trivial;
	wire [15:0] pout_special_or_trivial;
	handle_special_or_trivial #(.N(N)) handle_special_or_trivial_inst(
		.op_i(op_i),
		.p1_i(p1_i),
		.p2_i(p2_i),
		.p3_i(p3_i),
		.pout_o(pout_special_or_trivial)
	);
	localparam ppu_pkg_NAR = {1'b1, {15 {1'b0}}};
	localparam ppu_pkg_ZERO = {16 {1'b0}};
	assign is_special_or_trivial = (op_i == sv2v_cast_F65AF(6) ? 0 : (((((p1_i == ppu_pkg_ZERO) || (p1_i == ppu_pkg_NAR)) || (p2_i == ppu_pkg_ZERO)) || (p2_i == ppu_pkg_NAR)) || ((op_i == sv2v_cast_F65AF(1)) && (p1_i == p2_i))) || ((op_i == sv2v_cast_F65AF(0)) && (p1_i == ppu_pkg_c2(p2_i))));
	assign p_special_o[16-:ppu_pkg_N] = pout_special_or_trivial;
	assign p_special_o[0] = is_special_or_trivial;
endmodule
module extraction (
	p1_i,
	p2_i,
	p3_i,
	op_i,
	op_o,
	fir1_o,
	fir2_o,
	fir3_o,
	p_special_o
);
	parameter N = -1;
	localparam ppu_pkg_N = 16;
	input wire [15:0] p1_i;
	input wire [15:0] p2_i;
	input wire [15:0] p3_i;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	output wire [2:0] op_o;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	output wire [21:0] fir1_o;
	output wire [21:0] fir2_o;
	output wire [21:0] fir3_o;
	output wire [16:0] p_special_o;
	wire [15:0] p1_cond;
	wire [15:0] p2_cond;
	wire [15:0] p3_cond;
	input_conditioning #(.N(N)) input_conditioning(
		.p1_i(p1_i),
		.p2_i(p2_i),
		.p3_i(p3_i),
		.op_i(op_i),
		.p1_o(p1_cond),
		.p2_o(p2_cond),
		.p3_o(p3_cond),
		.p_special_o(p_special_o)
	);
	posit_to_fir #(
		.N(N),
		.ES(ppu_pkg_ES)
	) posit_to_fir1(
		.p_cond_i(p1_cond),
		.fir_o(fir1_o)
	);
	wire [N - 1:0] posit_in_posit_to_fir2;
	assign posit_in_posit_to_fir2 = p2_cond;
	posit_to_fir #(
		.N(N),
		.ES(ppu_pkg_ES)
	) posit_to_fir2(
		.p_cond_i(posit_in_posit_to_fir2),
		.fir_o(fir2_o)
	);
	posit_to_fir #(
		.N(N),
		.ES(ppu_pkg_ES)
	) posit_to_fir3(
		.p_cond_i(p3_cond),
		.fir_o(fir3_o)
	);
	assign op_o = op_i;
endmodule
module normalization (
	ops_result_i,
	p_special_i,
	posit_o
);
	parameter N = -1;
	parameter ES = -1;
	parameter FIR_TOTAL_SIZE = -1;
	parameter TE_BITS = -1;
	parameter FRAC_FULL_SIZE = -1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_RECIPROCATE_MANT_SIZE = 28;
	localparam ppu_pkg_RMS = ppu_pkg_RECIPROCATE_MANT_SIZE;
	localparam ppu_pkg_MANT_DIV_RESULT_SIZE = 42;
	localparam ppu_pkg_FRAC_FULL_SIZE = 40;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [48:0] ops_result_i;
	input wire [16:0] p_special_i;
	output wire [15:0] posit_o;
	wire [15:0] pout_non_special;
	fir_to_posit #(
		.N(N),
		.ES(ES),
		.FIR_TOTAL_SIZE(FIR_TOTAL_SIZE)
	) fir_to_posit_inst(
		.ops_result_i(ops_result_i),
		.posit_o(pout_non_special)
	);
	wire is_special_or_trivial;
	wire pout_special_or_trivial;
	assign is_special_or_trivial = p_special_i[0];
	assign pout_special_or_trivial = p_special_i[16-:16];
	assign posit_o = (is_special_or_trivial ? pout_special_or_trivial : pout_non_special);
endmodule
module handle_special_or_trivial (
	op_i,
	p1_i,
	p2_i,
	p3_i,
	pout_o
);
	parameter N = -1;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	localparam ppu_pkg_N = 16;
	input wire [15:0] p1_i;
	input wire [15:0] p2_i;
	input wire [15:0] p3_i;
	output wire [15:0] pout_o;
	wire [15:0] p_out_lut_mul;
	wire [15:0] p_out_lut_add;
	wire [15:0] p_out_lut_sub;
	wire [15:0] p_out_lut_div;
	lut_mul #(.N(N)) lut_mul_inst(
		.p1(p1_i),
		.p2(p2_i),
		.p_out(p_out_lut_mul)
	);
	lut_add #(.N(N)) lut_add_inst(
		.p1(p1_i),
		.p2(p2_i),
		.p_out(p_out_lut_add)
	);
	lut_sub #(.N(N)) lut_sub_inst(
		.p1(p1_i),
		.p2(p2_i),
		.p_out(p_out_lut_sub)
	);
	lut_div #(.N(N)) lut_div_inst(
		.p1(p1_i),
		.p2(p2_i),
		.p_out(p_out_lut_div)
	);
	function automatic [2:0] sv2v_cast_F65AF;
		input reg [2:0] inp;
		sv2v_cast_F65AF = inp;
	endfunction
	assign pout_o = (op_i == sv2v_cast_F65AF(2) ? p_out_lut_mul : (op_i == sv2v_cast_F65AF(0) ? p_out_lut_add : (op_i == sv2v_cast_F65AF(1) ? p_out_lut_sub : p_out_lut_div)));
endmodule
module lut_mul (
	p1,
	p2,
	p_out
);
	reg _sv2v_0;
	parameter N = -1;
	localparam ppu_pkg_N = 16;
	input wire [15:0] p1;
	input wire [15:0] p2;
	output reg [15:0] p_out;
	wire [(2 * N) - 1:0] addr;
	assign addr = {p1, p2};
	localparam ppu_pkg_NAR = {1'b1, {15 {1'b0}}};
	localparam ppu_pkg_ZERO = {16 {1'b0}};
	always @(*) begin
		if (_sv2v_0)
			;
		case (p1)
			ppu_pkg_ZERO: p_out = ((p2 == ppu_pkg_NAR) || (p2 == ppu_pkg_ZERO) ? p2 : ppu_pkg_ZERO);
			ppu_pkg_NAR: p_out = ppu_pkg_NAR;
			default: p_out = p2;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module lut_add (
	p1,
	p2,
	p_out
);
	reg _sv2v_0;
	parameter N = -1;
	localparam ppu_pkg_N = 16;
	input wire [15:0] p1;
	input wire [15:0] p2;
	output reg [15:0] p_out;
	localparam ppu_pkg_NAR = {1'b1, {15 {1'b0}}};
	localparam ppu_pkg_ZERO = {16 {1'b0}};
	function [15:0] ppu_pkg_c2;
		input [15:0] a;
		ppu_pkg_c2 = ~a + 1'b1;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		case (p1)
			ppu_pkg_ZERO: p_out = p2;
			ppu_pkg_NAR: p_out = ppu_pkg_NAR;
			default: p_out = (p2 == ppu_pkg_c2(p1) ? ppu_pkg_ZERO : (p2 == ppu_pkg_ZERO ? p1 : ppu_pkg_NAR));
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module lut_sub (
	p1,
	p2,
	p_out
);
	reg _sv2v_0;
	parameter N = -1;
	localparam ppu_pkg_N = 16;
	input wire [15:0] p1;
	input wire [15:0] p2;
	output reg [15:0] p_out;
	localparam ppu_pkg_NAR = {1'b1, {15 {1'b0}}};
	localparam ppu_pkg_ZERO = {16 {1'b0}};
	function [15:0] ppu_pkg_c2;
		input [15:0] a;
		ppu_pkg_c2 = ~a + 1'b1;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		case (p1)
			ppu_pkg_ZERO: p_out = ((p2 == ppu_pkg_ZERO) || (p2 == ppu_pkg_NAR) ? p2 : ppu_pkg_c2(p2));
			ppu_pkg_NAR: p_out = ppu_pkg_NAR;
			default: p_out = (p2 == p1 ? ppu_pkg_ZERO : (p2 == ppu_pkg_ZERO ? p1 : ppu_pkg_NAR));
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module lut_div (
	p1,
	p2,
	p_out
);
	reg _sv2v_0;
	parameter N = -1;
	localparam ppu_pkg_N = 16;
	input wire [15:0] p1;
	input wire [15:0] p2;
	output reg [15:0] p_out;
	localparam ppu_pkg_NAR = {1'b1, {15 {1'b0}}};
	localparam ppu_pkg_ZERO = {16 {1'b0}};
	always @(*) begin
		if (_sv2v_0)
			;
		case (p1)
			ppu_pkg_ZERO: p_out = ((p2 == ppu_pkg_NAR) || (p2 == ppu_pkg_ZERO) ? ppu_pkg_NAR : ppu_pkg_ZERO);
			ppu_pkg_NAR: p_out = ppu_pkg_NAR;
			default: p_out = ppu_pkg_NAR;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module total_exponent (
	k_i,
	exp_i,
	total_exp_o
);
	parameter N = -1;
	parameter ES = -1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_K_BITS = 6;
	input [5:0] k_i;
	input [ES - 1:0] exp_i;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_TE_BITS = 7;
	output wire [6:0] total_exp_o;
	assign total_exp_o = ($signed(k_i) >= 0 ? (k_i << ES) + exp_i : exp_i - ($signed(-k_i) << ES));
endmodule
module fir_ops (
	clk_i,
	rst_i,
	op_i,
	fir1_i,
	fir2_i,
	fir3_i,
	ops_result_o,
	fixed_o
);
	parameter N = -1;
	input wire clk_i;
	input wire rst_i;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [21:0] fir1_i;
	input wire [21:0] fir2_i;
	input wire [21:0] fir3_i;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_RECIPROCATE_MANT_SIZE = 28;
	localparam ppu_pkg_RMS = ppu_pkg_RECIPROCATE_MANT_SIZE;
	localparam ppu_pkg_MANT_DIV_RESULT_SIZE = 42;
	localparam ppu_pkg_FRAC_FULL_SIZE = 40;
	output wire [48:0] ops_result_o;
	output wire [63:0] fixed_o;
	wire [39:0] frac_out;
	wire sign_out;
	wire [6:0] te_out;
	wire [39:0] frac_full;
	wire frac_truncated;
	core_op #(
		.TE_BITS(ppu_pkg_TE_BITS),
		.MANT_SIZE(ppu_pkg_MANT_SIZE),
		.FRAC_FULL_SIZE(ppu_pkg_FRAC_FULL_SIZE)
	) core_op_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.op_i(op_i),
		.fir1_i(fir1_i),
		.fir2_i(fir2_i),
		.fir3_i(fir3_i),
		.sign_o(sign_out),
		.te_o(te_out),
		.frac_o(frac_out),
		.fixed_o(fixed_o),
		.frac_truncated_o(frac_truncated)
	);
	assign ops_result_o[48-:48] = {sign_out, te_out, frac_out};
	assign ops_result_o[0] = frac_truncated;
endmodule
module core_op (
	clk_i,
	rst_i,
	op_i,
	fir1_i,
	fir2_i,
	fir3_i,
	sign_o,
	te_o,
	frac_o,
	fixed_o,
	frac_truncated_o
);
	parameter TE_BITS = -1;
	parameter MANT_SIZE = -1;
	parameter FRAC_FULL_SIZE = -1;
	parameter FX_M = 31;
	parameter FX_B = 64;
	input clk_i;
	input rst_i;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [21:0] fir1_i;
	input wire [21:0] fir2_i;
	input wire [21:0] fir3_i;
	output wire sign_o;
	output wire [6:0] te_o;
	output wire [FRAC_FULL_SIZE - 1:0] frac_o;
	output wire [FX_B - 1:0] fixed_o;
	output wire frac_truncated_o;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_MAX_TE_DIFF = ppu_pkg_MS;
	localparam ppu_pkg_MTD = ppu_pkg_MAX_TE_DIFF;
	localparam ppu_pkg_MANT_ADD_RESULT_SIZE = 29;
	wire [28:0] mant_out_add_sub;
	localparam ppu_pkg_MANT_MUL_RESULT_SIZE = 28;
	wire [27:0] mant_out_mul;
	localparam ppu_pkg_RECIPROCATE_MANT_SIZE = 28;
	localparam ppu_pkg_RMS = ppu_pkg_RECIPROCATE_MANT_SIZE;
	localparam ppu_pkg_MANT_DIV_RESULT_SIZE = 42;
	wire [41:0] mant_out_div;
	wire sign_out_add_sub;
	wire sign_out_mul;
	wire sign_out_div;
	wire [6:0] te_out_add_sub;
	wire [6:0] te_out_mul;
	wire [6:0] te_out_div;
	wire frac_truncated_add_sub;
	wire frac_truncated_mul;
	wire frac_truncated_div;
	core_mul #(
		.TE_BITS(TE_BITS),
		.MANT_SIZE(MANT_SIZE),
		.MANT_MUL_RESULT_SIZE(ppu_pkg_MANT_MUL_RESULT_SIZE)
	) core_mul_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.sign1_i(fir1_i[21]),
		.sign2_i(fir2_i[21]),
		.te1_i(fir1_i[20-:7]),
		.te2_i(fir2_i[20-:7]),
		.mant1_i(fir1_i[13-:ppu_pkg_MANT_SIZE]),
		.mant2_i(fir2_i[13-:ppu_pkg_MANT_SIZE]),
		.sign_o(sign_out_mul),
		.te_o(te_out_mul),
		.mant_o(mant_out_mul),
		.frac_truncated_o(frac_truncated_mul)
	);
	wire [((1 + TE_BITS) + ppu_pkg_MANT_MUL_RESULT_SIZE) - 1:0] fir1_core_fma_accumulator;
	function automatic [2:0] sv2v_cast_F65AF;
		input reg [2:0] inp;
		sv2v_cast_F65AF = inp;
	endfunction
	assign fir1_core_fma_accumulator = ((op_i == sv2v_cast_F65AF(4)) || (op_i == sv2v_cast_F65AF(5)) ? {sign_out_mul, te_out_mul, mant_out_mul} : 'b0);
	wire [21:0] fir2_core_fma_accumulator;
	assign fir2_core_fma_accumulator = ((op_i == sv2v_cast_F65AF(4)) || (op_i == sv2v_cast_F65AF(5)) ? fir3_i : 'b0);
	localparam FIR_TE_SIZE = TE_BITS;
	localparam FIR_FRAC_SIZE = FRAC_FULL_SIZE;
	wire [((1 + FIR_TE_SIZE) + FIR_FRAC_SIZE) - 1:0] fir_fma;
	wire sign_out_fma;
	wire [TE_BITS - 1:0] te_out_fma;
	wire [FRAC_FULL_SIZE - 1:0] mant_out_fma;
	core_fma_accumulator #(
		.N(ppu_pkg_N),
		.TE_BITS(TE_BITS),
		.MANT_SIZE(MANT_SIZE),
		.FRAC_FULL_SIZE(FRAC_FULL_SIZE),
		.FX_M(FX_M),
		.FX_B(FX_B),
		.FIR_TE_SIZE(FIR_TE_SIZE),
		.FIR_FRAC_SIZE(FIR_FRAC_SIZE)
	) core_fma_accumulator_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.op_i(op_i),
		.fir1_i(fir1_core_fma_accumulator),
		.fir2_i(fir2_core_fma_accumulator),
		.fir_fma(fir_fma),
		.fixed_o(fixed_o)
	);
	assign {sign_out_fma, te_out_fma, mant_out_fma} = fir_fma;
	add_sub #(
		.TE_BITS(TE_BITS),
		.MANT_SIZE(MANT_SIZE),
		.MANT_ADD_RESULT_SIZE(ppu_pkg_MANT_ADD_RESULT_SIZE)
	) add_sub_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.sign1_i(fir1_i[21]),
		.sign2_i(fir2_i[21]),
		.te1_i(fir1_i[20-:7]),
		.te2_i(fir2_i[20-:7]),
		.mant1_i(fir1_i[13-:ppu_pkg_MANT_SIZE]),
		.mant2_i(fir2_i[13-:ppu_pkg_MANT_SIZE]),
		.sign_o(sign_out_add_sub),
		.te_o(te_out_add_sub),
		.mant_o(mant_out_add_sub),
		.frac_truncated_o(frac_truncated_add_sub)
	);
	core_div #(
		.TE_BITS(TE_BITS),
		.MANT_SIZE(MANT_SIZE),
		.MANT_DIV_RESULT_SIZE(ppu_pkg_MANT_DIV_RESULT_SIZE)
	) core_div_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.sign1_i(fir1_i[21]),
		.sign2_i(fir2_i[21]),
		.te1_i(fir1_i[20-:7]),
		.te2_i(fir2_i[20-:7]),
		.mant1_i(fir1_i[13-:ppu_pkg_MANT_SIZE]),
		.mant2_i(fir2_i[13-:ppu_pkg_MANT_SIZE]),
		.sign_o(sign_out_div),
		.te_o(te_out_div),
		.mant_o(mant_out_div),
		.frac_truncated_o(frac_truncated_div)
	);
	wire [FRAC_FULL_SIZE - 1:0] mant_out_core_op;
	assign mant_out_core_op = ((op_i == sv2v_cast_F65AF(0)) || (op_i == sv2v_cast_F65AF(1)) ? mant_out_add_sub << (FRAC_FULL_SIZE - ppu_pkg_MANT_ADD_RESULT_SIZE) : (op_i == sv2v_cast_F65AF(2) ? mant_out_mul << (FRAC_FULL_SIZE - ppu_pkg_MANT_MUL_RESULT_SIZE) : mant_out_div));
	assign sign_o = ((op_i == sv2v_cast_F65AF(4)) || (op_i == sv2v_cast_F65AF(5)) ? sign_out_fma : ((op_i == sv2v_cast_F65AF(0)) || (op_i == sv2v_cast_F65AF(1)) ? sign_out_add_sub : (op_i == sv2v_cast_F65AF(2) ? sign_out_mul : sign_out_div)));
	assign te_o = ((op_i == sv2v_cast_F65AF(4)) || (op_i == sv2v_cast_F65AF(5)) ? te_out_fma : ((op_i == sv2v_cast_F65AF(0)) || (op_i == sv2v_cast_F65AF(1)) ? te_out_add_sub : (op_i == sv2v_cast_F65AF(2) ? te_out_mul : te_out_div)));
	assign frac_o = ((op_i == sv2v_cast_F65AF(4)) || (op_i == sv2v_cast_F65AF(5)) ? mant_out_fma : (op_i == sv2v_cast_F65AF(3) ? mant_out_core_op : mant_out_core_op << 2));
	assign frac_truncated_o = (op_i == sv2v_cast_F65AF(2) ? frac_truncated_mul : (op_i == sv2v_cast_F65AF(3) ? frac_truncated_div : frac_truncated_add_sub));
endmodule
module core_add_sub (
	clk_i,
	rst_i,
	sign1_i,
	sign2_i,
	te1_i,
	te2_i,
	mant1_i,
	mant2_i,
	sign_o,
	te_o,
	mant_o,
	frac_truncated_o
);
	parameter TE_BITS = -1;
	parameter MANT_SIZE = -1;
	parameter MANT_ADD_RESULT_SIZE = -1;
	input wire clk_i;
	input wire rst_i;
	input wire sign1_i;
	input wire sign2_i;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [6:0] te1_i;
	input wire [6:0] te2_i;
	input [MANT_SIZE - 1:0] mant1_i;
	input [MANT_SIZE - 1:0] mant2_i;
	output wire sign_o;
	output wire [6:0] te_o;
	output wire [MANT_ADD_RESULT_SIZE - 1:0] mant_o;
	output wire frac_truncated_o;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_MAX_TE_DIFF = ppu_pkg_MS;
	function [(MANT_SIZE + ppu_pkg_MAX_TE_DIFF) - 1:0] _c2;
		input [(MANT_SIZE + ppu_pkg_MAX_TE_DIFF) - 1:0] a;
		_c2 = ~a + 1'b1;
	endfunction
	wire have_opposite_sign;
	assign have_opposite_sign = sign1_i ^ sign2_i;
	wire have_opposite_sign_st0;
	wire have_opposite_sign_st1;
	assign have_opposite_sign_st0 = have_opposite_sign;
	wire [6:0] te1;
	wire [6:0] te2_st0;
	wire [6:0] te2_st1;
	wire [MANT_SIZE - 1:0] mant1;
	wire [MANT_SIZE - 1:0] mant2;
	assign {te1, te2_st0} = {te1_i, te2_i};
	assign {mant1, mant2} = {mant1_i, mant2_i};
	wire [6:0] te_diff_st0;
	wire [6:0] te_diff_st1;
	assign te_diff_st0 = $signed(te1) - $signed(te2_st0);
	wire [(MANT_SIZE + ppu_pkg_MAX_TE_DIFF) - 1:0] mant1_upshifted;
	wire [(MANT_SIZE + ppu_pkg_MAX_TE_DIFF) - 1:0] mant2_upshifted;
	assign mant1_upshifted = mant1 << ppu_pkg_MAX_TE_DIFF;
	function [15:0] ppu_pkg_max;
		input [15:0] a;
		input [15:0] b;
		ppu_pkg_max = (a >= b ? a : b);
	endfunction
	assign mant2_upshifted = (mant2 << ppu_pkg_MAX_TE_DIFF) >> ppu_pkg_max(0, te_diff_st0);
	wire [MANT_ADD_RESULT_SIZE - 1:0] mant_sum_st0;
	wire [MANT_ADD_RESULT_SIZE - 1:0] mant_sum_st1;
	assign mant_sum_st0 = mant1_upshifted + (have_opposite_sign ? _c2(mant2_upshifted) : mant2_upshifted);
	wire [MANT_ADD_RESULT_SIZE - 1:0] mant_out_core_add;
	wire [6:0] te_diff_out_core_add;
	core_add #(
		.TE_BITS(TE_BITS),
		.MANT_ADD_RESULT_SIZE(MANT_ADD_RESULT_SIZE)
	) core_add_inst(
		.mant_i(mant_sum_st1),
		.te_diff_i(te_diff_st1),
		.new_mant_o(mant_out_core_add),
		.new_te_diff_o(te_diff_out_core_add),
		.frac_truncated_o(frac_truncated_o)
	);
	localparam ppu_pkg_MTD = ppu_pkg_MAX_TE_DIFF;
	localparam ppu_pkg_MANT_SUB_RESULT_SIZE = 28;
	wire [27:0] mant_out_core_sub;
	wire [6:0] te_diff_out_core_sub;
	core_sub #(
		.TE_BITS(TE_BITS),
		.MANT_SUB_RESULT_SIZE(ppu_pkg_MANT_SUB_RESULT_SIZE)
	) core_sub_inst(
		.mant(mant_sum_st1[27:0]),
		.te_diff(te_diff_st1),
		.new_mant(mant_out_core_sub),
		.new_te_diff(te_diff_out_core_sub)
	);
	wire [6:0] te_diff_updated;
	assign te_diff_updated = (have_opposite_sign_st1 ? te_diff_out_core_sub : te_diff_out_core_add);
	assign mant_o = (have_opposite_sign_st1 ? {mant_out_core_sub} : mant_out_core_add);
	assign te_o = te2_st1 + te_diff_updated;
	assign te_diff_st1 = te_diff_st0;
	assign mant_sum_st1 = mant_sum_st0;
	assign have_opposite_sign_st1 = have_opposite_sign_st0;
	assign te2_st1 = te2_st0;
	assign sign_o = sign1_i;
endmodule
module add_sub (
	clk_i,
	rst_i,
	sign1_i,
	sign2_i,
	te1_i,
	te2_i,
	mant1_i,
	mant2_i,
	sign_o,
	te_o,
	mant_o,
	frac_truncated_o
);
	parameter TE_BITS = -1;
	parameter MANT_SIZE = -1;
	parameter MANT_ADD_RESULT_SIZE = -1;
	input wire clk_i;
	input wire rst_i;
	input wire sign1_i;
	input wire sign2_i;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [6:0] te1_i;
	input wire [6:0] te2_i;
	input [MANT_SIZE - 1:0] mant1_i;
	input [MANT_SIZE - 1:0] mant2_i;
	output wire sign_o;
	output wire [6:0] te_o;
	output wire [MANT_ADD_RESULT_SIZE - 1:0] mant_o;
	output wire frac_truncated_o;
	wire sign1;
	wire sign2;
	wire [6:0] te1;
	wire [6:0] te2;
	wire [MANT_SIZE - 1:0] mant1;
	wire [MANT_SIZE - 1:0] mant2;
	router_core_add_sub #(.SIZE((1 + TE_BITS) + MANT_SIZE)) router_core_add_sub_i(
		.port1_i({sign1_i, te1_i, mant1_i}),
		.port2_i({sign2_i, te2_i, mant2_i}),
		.port1_o({sign1, te1, mant1}),
		.port2_o({sign2, te2, mant2})
	);
	core_add_sub #(
		.TE_BITS(TE_BITS),
		.MANT_SIZE(MANT_SIZE),
		.MANT_ADD_RESULT_SIZE(MANT_ADD_RESULT_SIZE)
	) core_add_sub_i(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.sign1_i(sign1),
		.sign2_i(sign2),
		.te1_i(te1),
		.te2_i(te2),
		.mant1_i(mant1),
		.mant2_i(mant2),
		.sign_o(sign_o),
		.te_o(te_o),
		.mant_o(mant_o),
		.frac_truncated_o(frac_truncated_o)
	);
endmodule
module router_core_add_sub (
	port1_i,
	port2_i,
	port1_o,
	port2_o
);
	parameter SIZE = -1;
	input wire [SIZE - 1:0] port1_i;
	input wire [SIZE - 1:0] port2_i;
	output wire [SIZE - 1:0] port1_o;
	output wire [SIZE - 1:0] port2_o;
	wire sign1_i;
	wire sign2_i;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	wire [6:0] te1_i;
	wire [6:0] te2_i;
	localparam ppu_pkg_MANT_SIZE = 14;
	wire [13:0] mant1_i;
	wire [13:0] mant2_i;
	assign {sign1_i, te1_i, mant1_i} = port1_i;
	assign {sign2_i, te2_i, mant2_i} = port2_i;
	wire sign1;
	wire sign2;
	wire [6:0] te1;
	wire [6:0] te2;
	wire [13:0] mant1;
	wire [13:0] mant2;
	assign {sign1, te1, mant1, sign2, te2, mant2} = ($signed(te1_i) < $signed(te2_i) ? {sign2_i, te2_i, mant2_i, sign1_i, te1_i, mant1_i} : ($signed(te1_i) == $signed(te2_i) ? (mant1_i < mant2_i ? {sign2_i, te2_i, mant2_i, sign1_i, te1_i, mant1_i} : {sign1_i, te1_i, mant1_i, sign2_i, te2_i, mant2_i}) : {sign1_i, te1_i, mant1_i, sign2_i, te2_i, mant2_i}));
	assign port1_o = {sign1, te1, mant1};
	assign port2_o = {sign2, te2, mant2};
endmodule
module core_add (
	mant_i,
	te_diff_i,
	new_mant_o,
	new_te_diff_o,
	frac_truncated_o
);
	parameter TE_BITS = -1;
	parameter MANT_ADD_RESULT_SIZE = -1;
	input [MANT_ADD_RESULT_SIZE - 1:0] mant_i;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [6:0] te_diff_i;
	output wire [MANT_ADD_RESULT_SIZE - 1:0] new_mant_o;
	output wire [6:0] new_te_diff_o;
	output wire frac_truncated_o;
	wire mant_carry;
	assign mant_carry = mant_i[MANT_ADD_RESULT_SIZE - 1];
	assign new_mant_o = (mant_carry == 1'b1 ? mant_i >> 1 : mant_i);
	assign new_te_diff_o = (mant_carry == 1'b1 ? te_diff_i + 1 : te_diff_i);
	assign frac_truncated_o = mant_carry && (mant_i & 1);
endmodule
module core_sub (
	mant,
	te_diff,
	new_mant,
	new_te_diff
);
	parameter TE_BITS = -1;
	parameter MANT_SUB_RESULT_SIZE = -1;
	input [MANT_SUB_RESULT_SIZE - 1:0] mant;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [6:0] te_diff;
	output wire [MANT_SUB_RESULT_SIZE - 1:0] new_mant;
	output wire [6:0] new_te_diff;
	wire [$clog2(MANT_SUB_RESULT_SIZE) - 1:0] leading_zeros;
	wire is_valid;
	lzc #(.NUM_BITS(MANT_SUB_RESULT_SIZE)) lzc_inst(
		.bits_i(mant),
		.lzc_o(leading_zeros),
		.valid_o(is_valid)
	);
	assign new_te_diff = te_diff - leading_zeros;
	assign new_mant = mant << leading_zeros;
endmodule
module core_mul (
	clk_i,
	rst_i,
	sign1_i,
	sign2_i,
	te1_i,
	te2_i,
	mant1_i,
	mant2_i,
	sign_o,
	te_o,
	mant_o,
	frac_truncated_o
);
	parameter TE_BITS = -1;
	parameter MANT_SIZE = -1;
	parameter MANT_MUL_RESULT_SIZE = -1;
	input clk_i;
	input rst_i;
	input wire sign1_i;
	input wire sign2_i;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [6:0] te1_i;
	input wire [6:0] te2_i;
	input [MANT_SIZE - 1:0] mant1_i;
	input [MANT_SIZE - 1:0] mant2_i;
	output wire sign_o;
	output wire [6:0] te_o;
	output wire [MANT_MUL_RESULT_SIZE - 1:0] mant_o;
	output wire frac_truncated_o;
	wire [6:0] te_sum_st0;
	wire [6:0] te_sum_st1;
	assign te_sum_st0 = te1_i + te2_i;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_MAX_TE_DIFF = ppu_pkg_MS;
	localparam ppu_pkg_MTD = ppu_pkg_MAX_TE_DIFF;
	localparam ppu_pkg_MANT_SUB_RESULT_SIZE = 28;
	wire [27:0] mant_mul;
	wire mant_carry;
	assign mant_carry = mant_mul[MANT_MUL_RESULT_SIZE - 1];
	assign te_o = (mant_carry == 1'b1 ? te_sum_st1 + 1'b1 : te_sum_st1);
	assign mant_o = (mant_carry == 1'b1 ? mant_mul >> 1 : mant_mul);
	assign frac_truncated_o = mant_carry && (mant_mul & 1);
	assign sign_o = sign1_i ^ sign2_i;
	assign te_sum_st1 = te_sum_st0;
	assign mant_mul = mant1_i * mant2_i;
endmodule
module core_fma_accumulator (
	clk_i,
	rst_i,
	op_i,
	fir1_i,
	fir2_i,
	fir_fma,
	fixed_o
);
	parameter N = -1;
	parameter TE_BITS = -1;
	parameter MANT_SIZE = -1;
	parameter FRAC_FULL_SIZE = -1;
	parameter FX_M = 31;
	parameter FX_B = 64;
	parameter FIR_TE_SIZE = -1;
	parameter FIR_FRAC_SIZE = -1;
	input wire clk_i;
	input wire rst_i;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_MANT_MUL_RESULT_SIZE = 28;
	input [((1 + TE_BITS) + ppu_pkg_MANT_MUL_RESULT_SIZE) - 1:0] fir1_i;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [21:0] fir2_i;
	output wire [((1 + FIR_TE_SIZE) + FIR_FRAC_SIZE) - 1:0] fir_fma;
	output wire [FX_B - 1:0] fixed_o;
	reg [2:0] op_st1;
	always @(posedge clk_i) op_st1 <= op_i;
	wire start_fma;
	function automatic [2:0] sv2v_cast_F65AF;
		input reg [2:0] inp;
		sv2v_cast_F65AF = inp;
	endfunction
	assign start_fma = op_i == sv2v_cast_F65AF(4);
	wire fma_valid;
	assign fma_valid = 1'b1;
	wire [FX_B - 1:0] fir1_fixed;
	wire [FX_B - 1:0] fir2_fixed;
	fir_to_fixed #(
		.N((2 * N) - 3),
		.FIR_TE_SIZE(TE_BITS),
		.FIR_FRAC_SIZE(ppu_pkg_MANT_MUL_RESULT_SIZE),
		.FX_M(FX_M),
		.FX_B(FX_B)
	) fir_to_fixed_1_mul(
		.fir_i(fir1_i),
		.fixed_o(fir1_fixed)
	);
	fir_to_fixed #(
		.N(N),
		.FIR_TE_SIZE(7),
		.FIR_FRAC_SIZE(14),
		.FX_M(FX_M),
		.FX_B(FX_B)
	) fir_to_fixed_2_fir3(
		.fir_i(fir2_i),
		.fixed_o(fir2_fixed)
	);
	wire [FX_B - 1:0] acc;
	accumulator #(.FIXED_SIZE(FX_B)) accumulator_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.start_i(start_fma),
		.init_value_i(fir2_fixed),
		.fixed_i(fir1_fixed),
		.fixed_o(acc)
	);
	fixed_to_fir #(
		.N(N),
		.FIR_TE_SIZE(TE_BITS),
		.FIR_FRAC_SIZE(FRAC_FULL_SIZE),
		.FX_M(FX_M),
		.FX_B(FX_B)
	) fixed_to_fir_acc(
		.fixed_i(acc),
		.fir_o(fir_fma)
	);
	assign fixed_o = acc;
endmodule
module core_div (
	clk_i,
	rst_i,
	sign1_i,
	sign2_i,
	te1_i,
	te2_i,
	mant1_i,
	mant2_i,
	sign_o,
	te_o,
	mant_o,
	frac_truncated_o
);
	parameter TE_BITS = -1;
	parameter MANT_SIZE = -1;
	parameter MANT_DIV_RESULT_SIZE = -1;
	input clk_i;
	input rst_i;
	input wire sign1_i;
	input wire sign2_i;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [6:0] te1_i;
	input wire [6:0] te2_i;
	input [MANT_SIZE - 1:0] mant1_i;
	input [MANT_SIZE - 1:0] mant2_i;
	output wire sign_o;
	output wire [6:0] te_o;
	output wire [MANT_DIV_RESULT_SIZE - 1:0] mant_o;
	output wire frac_truncated_o;
	wire [MANT_SIZE - 1:0] mant1_st0;
	wire [MANT_SIZE - 1:0] mant1_st1;
	assign mant1_st0 = mant1_i;
	wire [6:0] te_diff_st0;
	wire [6:0] te_diff_st1;
	assign te_diff_st0 = te1_i - te2_i;
	assign sign_o = sign1_i ^ sign2_i;
	wire [MANT_DIV_RESULT_SIZE - 1:0] mant_div;
	wire [(3 * MANT_SIZE) - 5:0] mant2_reciprocal;
	initial $display("***** Using DIV with Fast reciprocate algorithm, no LUT *****");
	fast_reciprocal #(.SIZE(MANT_SIZE)) fast_reciprocal_inst(
		.fraction(mant2_i),
		.one_over_fraction(mant2_reciprocal)
	);
	wire [(2 * MANT_SIZE) - 1:0] x1;
	initial $display("***** Using NR *****");
	newton_raphson #(.NR_SIZE(ppu_pkg_N)) newton_raphson_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.num_i(mant2_i),
		.x0_i(mant2_reciprocal),
		.x1_o(x1)
	);
	assign mant_div = mant1_st1 * x1;
	wire mant_div_less_than_one;
	assign mant_div_less_than_one = (mant_div & (1 << ((3 * MANT_SIZE) - 2))) == 0;
	assign mant_o = (mant_div_less_than_one ? mant_div << 1 : mant_div);
	assign te_o = (mant_div_less_than_one ? te_diff_st1 - 1 : te_diff_st1);
	assign frac_truncated_o = 1'b0;
	assign te_diff_st1 = te_diff_st0;
	assign mant1_st1 = mant1_st0;
endmodule
module fast_reciprocal (
	fraction,
	one_over_fraction
);
	parameter SIZE = -1;
	input [SIZE - 1:0] fraction;
	output wire [(3 * SIZE) - 5:0] one_over_fraction;
	wire [SIZE - 1:0] i_data;
	wire [(3 * SIZE) - 4:0] o_data;
	assign i_data = fraction >> 1;
	reciprocal_approx #(.SIZE(SIZE)) reciprocal_approx_inst(
		.i_data(i_data),
		.o_data(o_data)
	);
	assign one_over_fraction = o_data >> 1;
endmodule
module reciprocal_approx (
	i_data,
	o_data
);
	parameter SIZE = -1;
	input [SIZE - 1:0] i_data;
	output wire [(3 * SIZE) - 4:0] o_data;
	reg [SIZE - 1:0] a;
	reg [SIZE - 1:0] b;
	reg [(2 * SIZE) - 2:0] c;
	reg [(2 * SIZE) - 2:0] d;
	reg [(3 * SIZE) - 2:0] e;
	reg [(3 * SIZE) - 4:0] out;
	wire [SIZE:1] sv2v_tmp_758C5;
	assign sv2v_tmp_758C5 = i_data;
	always @(*) a = sv2v_tmp_758C5;
	localparam ppu_pkg_fx_1_466___N16 = 14'd11934;
	wire [SIZE - 1:0] fx_1_466 = ppu_pkg_fx_1_466___N16;
	localparam ppu_pkg_fx_1_0012___N16 = 27'd67171208;
	wire [(2 * SIZE) - 2:0] fx_1_0012 = ppu_pkg_fx_1_0012___N16;
	wire [SIZE:1] sv2v_tmp_8580D;
	assign sv2v_tmp_8580D = fx_1_466 - a;
	always @(*) b = sv2v_tmp_8580D;
	wire [(((2 * SIZE) - 2) >= 0 ? (2 * SIZE) - 1 : 3 - (2 * SIZE)):1] sv2v_tmp_D4E4B;
	assign sv2v_tmp_D4E4B = (($signed(a) * $signed(b)) << 1) >> 1;
	always @(*) c = sv2v_tmp_D4E4B;
	wire [(((2 * SIZE) - 2) >= 0 ? (2 * SIZE) - 1 : 3 - (2 * SIZE)):1] sv2v_tmp_1E38F;
	assign sv2v_tmp_1E38F = fx_1_0012 - c;
	always @(*) d = sv2v_tmp_1E38F;
	wire [(((3 * SIZE) - 2) >= 0 ? (3 * SIZE) - 1 : 3 - (3 * SIZE)):1] sv2v_tmp_1B67A;
	assign sv2v_tmp_1B67A = $signed(d) * $signed(b);
	always @(*) e = sv2v_tmp_1B67A;
	wire [(((3 * SIZE) - 4) >= 0 ? (3 * SIZE) - 3 : 5 - (3 * SIZE)):1] sv2v_tmp_CE844;
	assign sv2v_tmp_CE844 = e;
	always @(*) out = sv2v_tmp_CE844;
	assign o_data = out;
endmodule
module newton_raphson (
	clk_i,
	rst_i,
	num_i,
	x0_i,
	x1_o
);
	parameter NR_SIZE = -1;
	input clk_i;
	input rst_i;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	input [13:0] num_i;
	input [37:0] x0_i;
	output wire [27:0] x1_o;
	wire [52:0] _num_times_x0;
	assign _num_times_x0 = (num_i * x0_i) >> 24;
	wire [27:0] num_times_x0_st0;
	wire [27:0] num_times_x0_st1;
	assign num_times_x0_st0 = _num_times_x0;
	localparam ppu_pkg_fx_2___N16 = 28'd134217728;
	wire [27:0] fx_2 = ppu_pkg_fx_2___N16;
	wire [27:0] two_minus_num_x0;
	assign two_minus_num_x0 = fx_2 - num_times_x0_st1;
	wire [27:0] x0_on_2n_bits_st0;
	wire [27:0] x0_on_2n_bits_st1;
	assign x0_on_2n_bits_st0 = x0_i >> 10;
	wire [55:0] _x1;
	assign _x1 = x0_on_2n_bits_st1 * two_minus_num_x0;
	assign x1_o = _x1 >> 26;
	assign num_times_x0_st1 = num_times_x0_st0;
	assign x0_on_2n_bits_st1 = x0_on_2n_bits_st0;
endmodule
module pack_fields (
	frac_full_i,
	total_exp_i,
	frac_truncated_i,
	k_o,
	next_exp_o,
	frac_o,
	round_bit,
	sticky_bit,
	k_is_oob,
	non_zero_frac_field_size
);
	parameter N = -1;
	parameter ES = -1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_RECIPROCATE_MANT_SIZE = 28;
	localparam ppu_pkg_RMS = ppu_pkg_RECIPROCATE_MANT_SIZE;
	localparam ppu_pkg_MANT_DIV_RESULT_SIZE = 42;
	localparam ppu_pkg_FRAC_FULL_SIZE = 40;
	input [39:0] frac_full_i;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [6:0] total_exp_i;
	input frac_truncated_i;
	localparam ppu_pkg_K_BITS = 6;
	output wire [5:0] k_o;
	output wire [ES - 1:0] next_exp_o;
	output wire [13:0] frac_o;
	output wire round_bit;
	output wire sticky_bit;
	output wire k_is_oob;
	output wire non_zero_frac_field_size;
	wire [5:0] k_unpacked;
	wire [ES - 1:0] exp_unpacked;
	unpack_exponent #(
		.N(N),
		.ES(ES)
	) unpack_exponent_inst(
		.total_exp_i(total_exp_i),
		.k_o(k_unpacked),
		.exp_o(exp_unpacked)
	);
	wire [5:0] regime_k;
	assign regime_k = (($signed(k_unpacked) <= (N - 2)) && ($signed(k_unpacked) >= (2 - N)) ? $signed(k_unpacked) : ($signed(k_unpacked) >= 0 ? N - 2 : 2 - N));
	assign k_is_oob = k_unpacked != regime_k;
	localparam ppu_pkg_REG_LEN_BITS = 5;
	wire [4:0] reg_len;
	assign reg_len = ($signed(regime_k) >= 0 ? regime_k + 2 : 1 - $signed(regime_k));
	localparam ppu_pkg_MANT_LEN_BITS = 5;
	wire [4:0] frac_len;
	assign frac_len = ((N - 1) - ES) - reg_len;
	wire [ES + 0:0] es_actual_len;
	function [15:0] ppu_pkg_min;
		input [15:0] a;
		input [15:0] b;
		ppu_pkg_min = ($signed(a) <= $signed(b) ? a : b);
	endfunction
	assign es_actual_len = ppu_pkg_min(ES, (N - 1) - reg_len);
	wire [ES - 1:0] exp1;
	function [15:0] ppu_pkg_max;
		input [15:0] a;
		input [15:0] b;
		ppu_pkg_max = (a >= b ? a : b);
	endfunction
	assign exp1 = exp_unpacked >> ppu_pkg_max(0, ES - es_actual_len);
	wire [5:0] frac_len_diff;
	assign frac_len_diff = ppu_pkg_FRAC_FULL_SIZE - $signed(frac_len);
	compute_rouding #(
		.N(N),
		.ES(ES)
	) compute_rouding_inst(
		.frac_len_i(frac_len),
		.frac_full_i(frac_full_i),
		.frac_len_diff_i(frac_len_diff),
		.k_i(regime_k),
		.exp_i(exp_unpacked),
		.frac_truncated_i(frac_truncated_i),
		.round_bit_o(round_bit),
		.sticky_bit_o(sticky_bit)
	);
	assign k_o = regime_k;
	wire [ES - 1:0] exp2;
	assign exp2 = exp1 << (ES - es_actual_len);
	assign frac_o = frac_full_i >> frac_len_diff;
	assign non_zero_frac_field_size = $signed(frac_len) >= 0;
	assign next_exp_o = exp2;
endmodule
module unpack_exponent (
	total_exp_i,
	k_o,
	exp_o
);
	parameter N = -1;
	parameter ES = -1;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [6:0] total_exp_i;
	localparam ppu_pkg_K_BITS = 6;
	output wire [5:0] k_o;
	output wire [ES - 1:0] exp_o;
	assign k_o = total_exp_i >> ES;
	assign exp_o = total_exp_i - ((1 << ES) * k_o);
endmodule
module compute_rouding (
	frac_len_i,
	frac_full_i,
	frac_len_diff_i,
	k_i,
	exp_i,
	frac_truncated_i,
	round_bit_o,
	sticky_bit_o
);
	parameter N = -1;
	parameter ES = -1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_MANT_LEN_BITS = 5;
	input [4:0] frac_len_i;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_RECIPROCATE_MANT_SIZE = 28;
	localparam ppu_pkg_RMS = ppu_pkg_RECIPROCATE_MANT_SIZE;
	localparam ppu_pkg_MANT_DIV_RESULT_SIZE = 42;
	localparam ppu_pkg_FRAC_FULL_SIZE = 40;
	input [39:0] frac_full_i;
	input [5:0] frac_len_diff_i;
	localparam ppu_pkg_K_BITS = 6;
	input [5:0] k_i;
	input [ES - 1:0] exp_i;
	input frac_truncated_i;
	output wire round_bit_o;
	output wire sticky_bit_o;
	wire [43:0] _tmp0;
	wire [43:0] _tmp1;
	wire [43:0] _tmp2;
	wire [43:0] _tmp3;
	assign _tmp0 = 1 << (frac_len_diff_i - 1);
	assign _tmp1 = frac_full_i & _tmp0;
	assign round_bit_o = ($signed(frac_len_i) >= 0 ? _tmp1 != 0 : ($signed(k_i) == ((N - 2) - ES) ? (exp_i > 0) && ($unsigned(frac_full_i) > 0) : ($signed(k_i) == (2 - N) ? exp_i > 0 : 1'b0)));
	assign _tmp2 = (1 << (frac_len_diff_i - 1)) - 1;
	assign _tmp3 = frac_full_i & _tmp2;
	assign sticky_bit_o = ($signed(frac_len_i) >= 0 ? (_tmp3 != 0) || frac_truncated_i : 1'b0);
endmodule
module posit_unpack (
	bits_i,
	sign_o,
	reg_s_o,
	reg_len_o,
	k_o,
	exp_o,
	mant_o
);
	parameter N = 5;
	parameter ES = 0;
	localparam ppu_pkg_N = 16;
	input wire [15:0] bits_i;
	output wire sign_o;
	output wire reg_s_o;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_REG_LEN_BITS = 5;
	output wire [4:0] reg_len_o;
	localparam ppu_pkg_K_BITS = 6;
	output wire [5:0] k_o;
	output wire [ES - 1:0] exp_o;
	localparam ppu_pkg_MANT_SIZE = 14;
	output wire [13:0] mant_o;
	assign sign_o = bits_i[N - 1];
	wire [N - 1:0] u_bits;
	function [15:0] ppu_pkg_c2;
		input [15:0] a;
		ppu_pkg_c2 = ~a + 1'b1;
	endfunction
	assign u_bits = (sign_o == 0 ? bits_i : ppu_pkg_c2(bits_i));
	wire [3:0] leading_set;
	wire [3:0] leading_set_2;
	assign reg_s_o = u_bits[N - 2];
	wire is_special_case;
	assign is_special_case = bits_i == {1'b1, {N - 2 {1'b0}}, 1'b1};
	assign leading_set_2 = (is_special_case ? N - 1 : leading_set);
	assign k_o = (reg_s_o == 1 ? leading_set_2 - 1 : ppu_pkg_c2(leading_set_2));
	assign reg_len_o = (reg_s_o == 1 ? k_o + 2 : ppu_pkg_c2(k_o) + 1);
	assign exp_o = (u_bits << (1 + reg_len_o)) >> (N - ES);
	wire [4:0] mant_len;
	assign mant_len = ((N - 1) - reg_len_o) - ES;
	localparam ppu_pkg_FRAC_SIZE = 15;
	wire [14:0] frac;
	assign frac = (u_bits << (N - mant_len)) >> (N - mant_len);
	parameter MSB = 8192;
	assign mant_o = MSB | (frac << ((ppu_pkg_MANT_SIZE - mant_len) - 1));
	wire [N - 1:0] bits_cls_in = (sign_o == 0 ? u_bits : ~u_bits);
	wire val = bits_cls_in[N - 2];
	wire [3:0] leading_set_out_lzc;
	wire lzc_is_valid;
	lzc #(.NUM_BITS(N)) lzc_inst(
		.bits_i((val == 1'b0 ? bits_cls_in : ~bits_cls_in) << 1),
		.lzc_o(leading_set_out_lzc),
		.valid_o(lzc_is_valid)
	);
	assign leading_set = (lzc_is_valid == 1'b1 ? leading_set_out_lzc : N - 1);
endmodule
module posit_decoder (
	bits_i,
	fir_o
);
	parameter N = -1;
	parameter ES = -1;
	localparam ppu_pkg_N = 16;
	input wire [15:0] bits_i;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	output wire [21:0] fir_o;
	wire _reg_s;
	localparam ppu_pkg_REG_LEN_BITS = 5;
	wire [4:0] _reg_len;
	localparam ppu_pkg_K_BITS = 6;
	wire [5:0] k;
	wire [ES - 1:0] exp;
	wire sign;
	wire [6:0] total_exponent;
	wire [13:0] mant;
	posit_unpack #(
		.N(N),
		.ES(ES)
	) posit_unpack_inst(
		.bits_i(bits_i),
		.sign_o(sign),
		.reg_s_o(_reg_s),
		.reg_len_o(_reg_len),
		.k_o(k),
		.exp_o(exp),
		.mant_o(mant)
	);
	total_exponent #(
		.N(N),
		.ES(ES)
	) total_exponent_inst(
		.k_i(k),
		.exp_i(exp),
		.total_exp_o(total_exponent)
	);
	assign fir_o[21] = sign;
	assign fir_o[20-:7] = total_exponent;
	assign fir_o[13-:ppu_pkg_MANT_SIZE] = mant;
endmodule
module posit_encoder (
	is_zero_i,
	is_nar_i,
	sign,
	k,
	exp,
	frac,
	posit
);
	parameter N = 4;
	parameter ES = 1;
	input is_zero_i;
	input is_nar_i;
	input sign;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_K_BITS = 6;
	input [5:0] k;
	input [ES - 1:0] exp;
	localparam ppu_pkg_MANT_SIZE = 14;
	input [13:0] frac;
	output wire [N - 1:0] posit;
	localparam ppu_pkg_REG_LEN_BITS = 5;
	wire [4:0] reg_len;
	assign reg_len = ($signed(k) >= 0 ? k + 2 : 1 - $signed(k));
	wire [N - 1:0] bits_packed;
	wire [N:0] regime_bits;
	function ppu_pkg_is_negative;
		input [ppu_pkg_S:0] k;
		ppu_pkg_is_negative = k[ppu_pkg_S];
	endfunction
	function [15:0] ppu_pkg_c2;
		input [15:0] a;
		ppu_pkg_c2 = ~a + 1'b1;
	endfunction
	function [15:0] ppu_pkg_shl;
		input [15:0] bits;
		input [15:0] rhs;
		ppu_pkg_shl = (rhs[15] == 0 ? bits << rhs : bits >> ppu_pkg_c2(rhs));
	endfunction
	assign regime_bits = (ppu_pkg_is_negative(k) ? 1 : (ppu_pkg_shl(1, k + 1) - 1) << 1);
	assign bits_packed = ((ppu_pkg_shl(sign, N - 1) + ppu_pkg_shl(regime_bits, (N - 1) - reg_len)) + ppu_pkg_shl(exp, ((N - 1) - reg_len) - ES)) + frac;
	assign posit = (sign == 0 ? bits_packed : ppu_pkg_c2(bits_packed & ~(1 << (N - 1))));
endmodule
module lzc (
	bits_i,
	lzc_o,
	valid_o
);
	parameter NUM_BITS = -1;
	input [NUM_BITS - 1:0] bits_i;
	output wire [$clog2(NUM_BITS) - 1:0] lzc_o;
	output wire valid_o;
	lzc_internal #(.NUM_BITS(NUM_BITS)) l1(
		.in(bits_i),
		.out(lzc_o),
		.vld(valid_o)
	);
endmodule
module lzc_internal (
	in,
	out,
	vld
);
	parameter NUM_BITS = 8;
	input [NUM_BITS - 1:0] in;
	output wire [$clog2(NUM_BITS) - 1:0] out;
	output wire vld;
	localparam S = $clog2(NUM_BITS);
	generate
		if (NUM_BITS == 2) begin : gen_blk1
			assign vld = |in;
			assign out = ~in[1] & in[0];
		end
		else if (NUM_BITS & (NUM_BITS - 1)) begin : gen_blk2
			lzc_internal #(.NUM_BITS(1 << S)) lzc_internal(
				.in({in, {(1 << S) - NUM_BITS {1'b0}}}),
				.out(out),
				.vld(vld)
			);
		end
		else begin : gen_blk3
			wire [S - 2:0] out_l;
			wire [S - 2:0] out_h;
			wire out_vl;
			wire out_vh;
			lzc_internal #(.NUM_BITS(NUM_BITS >> 1)) lzc_internal_l(
				.in(in[(NUM_BITS >> 1) - 1:0]),
				.out(out_l),
				.vld(out_vl)
			);
			lzc_internal #(.NUM_BITS(NUM_BITS >> 1)) lzc_internal_h(
				.in(in[NUM_BITS - 1:NUM_BITS >> 1]),
				.out(out_h),
				.vld(out_vh)
			);
			assign vld = out_vl | out_vh;
			assign out = (out_vh ? {1'b0, out_h} : {out_vl, out_l});
		end
	endgenerate
endmodule
module round_posit (
	posit,
	round_bit,
	sticky_bit,
	k_is_oob,
	non_zero_frac_field_size,
	posit_rounded
);
	parameter N = 10;
	input [N - 1:0] posit;
	input round_bit;
	input sticky_bit;
	input k_is_oob;
	input non_zero_frac_field_size;
	output wire [N - 1:0] posit_rounded;
	wire guard_bit;
	assign guard_bit = posit[0];
	assign posit_rounded = ((!k_is_oob && round_bit) && (!non_zero_frac_field_size || (guard_bit || sticky_bit)) ? posit + 1'b1 : posit);
endmodule
module set_sign (
	posit_in,
	sign,
	posit_out
);
	parameter N = 9;
	input [N - 1:0] posit_in;
	input sign;
	output wire [N - 1:0] posit_out;
	localparam ppu_pkg_N = 16;
	function [15:0] ppu_pkg_c2;
		input [15:0] a;
		ppu_pkg_c2 = ~a + 1'b1;
	endfunction
	assign posit_out = (sign == 0 ? posit_in : ppu_pkg_c2(posit_in));
endmodule
module ppu (
	clk_i,
	rst_i,
	in_valid_i,
	operand1_i,
	operand2_i,
	operand3_i,
	op_i,
	result_o,
	out_valid_o,
	fixed_o
);
	parameter WORD = 32;
	parameter FSIZE = 32;
	parameter N = 16;
	parameter ES = 1;
	input wire clk_i;
	input wire rst_i;
	input wire in_valid_i;
	input wire [31:0] operand1_i;
	input wire [31:0] operand2_i;
	input wire [31:0] operand3_i;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	output wire [31:0] result_o;
	output wire out_valid_o;
	output wire [63:0] fixed_o;
	wire stall;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	wire [21:0] posit_fir;
	wire [15:0] p1;
	wire [15:0] p2;
	wire [15:0] p3;
	wire [15:0] posit;
	assign p1 = operand1_i[N - 1:0];
	assign p2 = operand2_i[N - 1:0];
	assign p3 = operand3_i[N - 1:0];
	localparam ppu_pkg_FLOAT_EXP_SIZE_F32 = 8;
	localparam ppu_pkg_FLOAT_MANT_SIZE_F32 = 23;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_RECIPROCATE_MANT_SIZE = 28;
	localparam ppu_pkg_RMS = ppu_pkg_RECIPROCATE_MANT_SIZE;
	localparam ppu_pkg_MANT_DIV_RESULT_SIZE = 42;
	localparam ppu_pkg_FRAC_FULL_SIZE = 40;
	wire [31:0] float_fir_float_to_fir_o;
	wire [47:0] float_fir_ppu_core_ops_i;
	assign float_fir_ppu_core_ops_i[47] = float_fir_float_to_fir_o[31];
	assign float_fir_ppu_core_ops_i[46-:7] = float_fir_float_to_fir_o[30-:8];
	assign float_fir_ppu_core_ops_i[39-:ppu_pkg_FRAC_FULL_SIZE] = {float_fir_float_to_fir_o[22-:ppu_pkg_FLOAT_MANT_SIZE_F32]} << 17;
	float_to_fir #(.FSIZE(FSIZE)) float_to_fir_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.bits_i(operand1_i),
		.fir_o(float_fir_float_to_fir_o)
	);
	ppu_core_ops #(
		.N(N),
		.ES(ES)
	) ppu_core_ops_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.p1_i(p1),
		.p2_i(p2),
		.p3_i(p3),
		.op_i(op_i),
		.op_o(),
		.stall_i(stall),
		.float_fir_i(float_fir_ppu_core_ops_i),
		.posit_fir_o(posit_fir),
		.pout_o(posit),
		.fixed_o(fixed_o)
	);
	wire [31:0] float_out;
	fir_to_float #(
		.N(N),
		.ES(ES),
		.FSIZE(FSIZE)
	) fir_to_float_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.fir_i(posit_fir),
		.float_o(float_out)
	);
	function automatic [2:0] sv2v_cast_F65AF;
		input reg [2:0] inp;
		sv2v_cast_F65AF = inp;
	endfunction
	assign result_o = (op_i == sv2v_cast_F65AF(7) ? float_out : posit);
	ppu_control_unit ppu_control_unit_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.valid_i(in_valid_i),
		.op_i(op_i),
		.valid_o(out_valid_o),
		.stall_o(stall)
	);
endmodule
module pipeline (
	clk_i,
	rst_i,
	data_in,
	data_out
);
	parameter PIPELINE_DEPTH = 2;
	parameter DATA_WIDTH = 32;
	input wire clk_i;
	input wire rst_i;
	input wire [DATA_WIDTH - 1:0] data_in;
	output wire [DATA_WIDTH - 1:0] data_out;
	generate
		if (PIPELINE_DEPTH == 0) begin : genblk1
			assign data_out = data_in;
		end
		else begin : genblk1
			(* retiming_backward = 1 *) reg [DATA_WIDTH - 1:0] pipeline_reg [PIPELINE_DEPTH - 1:0];
			always @(posedge clk_i)
				if (rst_i) begin : sv2v_autoblock_1
					reg signed [31:0] i;
					for (i = 0; i < PIPELINE_DEPTH; i = i + 1)
						pipeline_reg[i] <= 'b0;
				end
				else begin
					pipeline_reg[0] <= data_in;
					begin : sv2v_autoblock_2
						reg signed [31:0] i;
						for (i = 1; i < PIPELINE_DEPTH; i = i + 1)
							pipeline_reg[i] <= pipeline_reg[i - 1];
					end
				end
			assign data_out = pipeline_reg[PIPELINE_DEPTH - 1];
		end
	endgenerate
endmodule
module ppu_top (
	clk_i,
	rst_i,
	in_valid_i,
	operand1_i,
	operand2_i,
	operand3_i,
	op_i,
	result_o,
	out_valid_o,
	fixed_o
);
	parameter PIPELINE_DEPTH = 0;
	parameter WORD = 32;
	parameter FSIZE = 32;
	parameter N = 16;
	parameter ES = 1;
	input wire clk_i;
	input wire rst_i;
	input wire in_valid_i;
	input wire [WORD - 1:0] operand1_i;
	input wire [WORD - 1:0] operand2_i;
	input wire [WORD - 1:0] operand3_i;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	output wire [WORD - 1:0] result_o;
	output wire out_valid_o;
	output wire [63:0] fixed_o;
	wire [31:0] operand1_st0;
	wire [31:0] operand2_st0;
	wire [31:0] operand3_st0;
	wire [31:0] result_st0;
	wire [31:0] result_st1;
	wire [2:0] op_st0;
	wire in_valid_st0;
	wire out_valid_st0;
	wire out_valid_st1;
	wire [63:0] fixed_st0;
	function automatic [2:0] sv2v_cast_F65AF;
		input reg [2:0] inp;
		sv2v_cast_F65AF = inp;
	endfunction
	ppu #(
		.WORD(WORD),
		.FSIZE(FSIZE),
		.N(N),
		.ES(ES)
	) ppu_inst(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.in_valid_i(in_valid_st0),
		.operand1_i(operand1_st0),
		.operand2_i(operand2_st0),
		.operand3_i(operand3_st0),
		.op_i(sv2v_cast_F65AF(op_st0)),
		.result_o(result_st0),
		.out_valid_o(out_valid_st0),
		.fixed_o(fixed_st0)
	);
	localparam PIPELINE_DEPTH_FRONT = (PIPELINE_DEPTH >= 1 ? 1 : 0);
	localparam PIPELINE_DEPTH_BACK = (PIPELINE_DEPTH >= 1 ? PIPELINE_DEPTH - PIPELINE_DEPTH_FRONT : 0);
	initial $display("PIPELINE_DEPTH_FRONT = %0d", PIPELINE_DEPTH_FRONT);
	initial $display("PIPELINE_DEPTH_BACK = %0d", PIPELINE_DEPTH_BACK);
	pipeline #(
		.PIPELINE_DEPTH(PIPELINE_DEPTH_FRONT),
		.DATA_WIDTH(4 + (3 * WORD))
	) pipeline_front(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.data_in({in_valid_i, op_i, operand1_i, operand2_i, operand3_i}),
		.data_out({in_valid_st0, op_st0, operand1_st0, operand2_st0, operand3_st0})
	);
	pipeline #(
		.PIPELINE_DEPTH(PIPELINE_DEPTH_BACK),
		.DATA_WIDTH(97)
	) pipeline_back(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.data_in({result_st0, out_valid_st0, fixed_st0}),
		.data_out({result_o, out_valid_o, fixed_o})
	);
endmodule
module ppu_control_unit (
	clk_i,
	rst_i,
	valid_i,
	op_i,
	valid_o,
	stall_o
);
	input clk_i;
	input rst_i;
	input valid_i;
	localparam ppu_pkg_OP_BITS = 3;
	input wire [2:0] op_i;
	output wire valid_o;
	output wire stall_o;
	pipeline #(
		.PIPELINE_DEPTH(0),
		.DATA_WIDTH(1)
	) valid_signal_delay(
		.clk_i(clk_i),
		.rst_i(rst_i),
		.data_in(valid_i),
		.data_out(valid_o)
	);
endmodule
module float_to_fir (
	clk_i,
	rst_i,
	bits_i,
	fir_o
);
	parameter FSIZE = 64;
	input clk_i;
	input rst_i;
	input [FSIZE - 1:0] bits_i;
	localparam ppu_pkg_FLOAT_EXP_SIZE_F32 = 8;
	localparam ppu_pkg_FLOAT_MANT_SIZE_F32 = 23;
	output wire [31:0] fir_o;
	wire sign_st0;
	wire sign_st1;
	wire signed [7:0] exp_st0;
	wire signed [7:0] exp_st1;
	wire [22:0] frac_st0;
	wire [22:0] frac_st1;
	float_decoder #(.FSIZE(FSIZE)) float_decoder_inst(
		.bits(bits_i),
		.sign(sign_st0),
		.exp(exp_st0),
		.frac(frac_st0)
	);
	assign sign_st1 = sign_st0;
	assign exp_st1 = exp_st0;
	assign frac_st1 = frac_st0;
	assign fir_o = {sign_st1, exp_st1, frac_st1};
endmodule
module fir_to_float (
	clk_i,
	rst_i,
	fir_i,
	float_o
);
	parameter N = -1;
	parameter ES = -1;
	parameter FSIZE = -1;
	input clk_i;
	input rst_i;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [21:0] fir_i;
	output wire [FSIZE - 1:0] float_o;
	localparam ppu_pkg_FLOAT_EXP_SIZE_F32 = 8;
	parameter FLOAT_EXP_SIZE = ppu_pkg_FLOAT_EXP_SIZE_F32;
	localparam ppu_pkg_FLOAT_MANT_SIZE_F32 = 23;
	parameter FLOAT_MANT_SIZE = ppu_pkg_FLOAT_MANT_SIZE_F32;
	wire [21:0] fir_st0;
	wire [21:0] fir_st1;
	assign fir_st0 = fir_i;
	assign fir_st1 = fir_st0;
	wire posit_sign;
	wire [6:0] posit_te;
	wire [13:0] posit_frac;
	assign {posit_sign, posit_te, posit_frac} = fir_st1;
	wire float_sign;
	wire signed [FLOAT_EXP_SIZE - 1:0] float_exp;
	wire [FLOAT_MANT_SIZE - 1:0] float_frac;
	assign float_sign = posit_sign;
	sign_extend #(
		.POSIT_TOTAL_EXPONENT_SIZE(ppu_pkg_TE_BITS),
		.FLOAT_EXPONENT_SIZE(FLOAT_EXP_SIZE)
	) sign_extend_inst(
		.posit_total_exponent(posit_te),
		.float_exponent(float_exp)
	);
	assign float_frac = posit_frac << ((FLOAT_MANT_SIZE - ppu_pkg_MANT_SIZE) + 1);
	float_encoder #(.FSIZE(FSIZE)) float_encoder_inst(
		.sign(float_sign),
		.exp(float_exp),
		.frac(float_frac),
		.bits(float_o)
	);
endmodule
module sign_extend (
	posit_total_exponent,
	float_exponent
);
	parameter POSIT_TOTAL_EXPONENT_SIZE = 4;
	parameter FLOAT_EXPONENT_SIZE = 18;
	input [POSIT_TOTAL_EXPONENT_SIZE - 1:0] posit_total_exponent;
	output wire [FLOAT_EXPONENT_SIZE - 1:0] float_exponent;
	assign float_exponent = $signed(posit_total_exponent);
endmodule
module float_encoder (
	sign,
	exp,
	frac,
	bits
);
	parameter FSIZE = 32;
	input sign;
	localparam ppu_pkg_FLOAT_EXP_SIZE_F32 = 8;
	input signed [7:0] exp;
	localparam ppu_pkg_FLOAT_MANT_SIZE_F32 = 23;
	input [22:0] frac;
	output wire [FSIZE - 1:0] bits;
	wire [7:0] exp_bias = 127;
	wire [7:0] exp_biased;
	assign exp_biased = exp + exp_bias;
	assign bits = {sign, exp_biased, frac};
endmodule
module float_decoder (
	bits,
	sign,
	exp,
	frac
);
	parameter FSIZE = 64;
	input [FSIZE - 1:0] bits;
	output wire sign;
	localparam ppu_pkg_FLOAT_EXP_SIZE_F32 = 8;
	output wire signed [7:0] exp;
	localparam ppu_pkg_FLOAT_MANT_SIZE_F32 = 23;
	output wire [22:0] frac;
	localparam EXP_BIAS = 127;
	assign sign = (bits >> (FSIZE - 1)) != 0;
	wire [7:0] biased_exp;
	assign biased_exp = bits[FSIZE - 1-:9];
	assign exp = biased_exp - EXP_BIAS;
	assign frac = bits[22:0];
endmodule
module posit_to_fir (
	p_cond_i,
	fir_o
);
	parameter N = -1;
	parameter ES = -1;
	localparam ppu_pkg_N = 16;
	input wire [15:0] p_cond_i;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	output wire [21:0] fir_o;
	posit_decoder #(
		.N(N),
		.ES(ES)
	) posit_decoder_inst(
		.bits_i(p_cond_i),
		.fir_o(fir_o)
	);
endmodule
module fir_to_posit (
	ops_result_i,
	posit_o
);
	parameter N = -1;
	parameter ES = -1;
	parameter FIR_TOTAL_SIZE = -1;
	localparam ppu_pkg_N = 16;
	localparam ppu_pkg_MANT_SIZE = 14;
	localparam ppu_pkg_MS = ppu_pkg_MANT_SIZE;
	localparam ppu_pkg_RECIPROCATE_MANT_SIZE = 28;
	localparam ppu_pkg_RMS = ppu_pkg_RECIPROCATE_MANT_SIZE;
	localparam ppu_pkg_MANT_DIV_RESULT_SIZE = 42;
	localparam ppu_pkg_FRAC_FULL_SIZE = 40;
	localparam ppu_pkg_ES = 1;
	localparam ppu_pkg_S = 4;
	localparam ppu_pkg_TE_BITS = 7;
	input wire [48:0] ops_result_i;
	output wire [15:0] posit_o;
	wire [47:0] fir;
	assign fir = ops_result_i[48-:48];
	wire frac_truncated;
	assign frac_truncated = ops_result_i[0];
	wire sign;
	wire [6:0] te;
	wire [39:0] frac_full;
	assign {sign, te, frac_full} = fir;
	wire [13:0] frac;
	localparam ppu_pkg_K_BITS = 6;
	wire [5:0] k;
	wire [ES - 1:0] next_exp;
	wire round_bit;
	wire sticky_bit;
	wire k_is_oob;
	wire non_zero_frac_field_size;
	pack_fields #(
		.N(N),
		.ES(ES)
	) pack_fields_inst(
		.frac_full_i(frac_full),
		.total_exp_i(te),
		.frac_truncated_i(frac_truncated),
		.k_o(k),
		.next_exp_o(next_exp),
		.frac_o(frac),
		.round_bit(round_bit),
		.sticky_bit(sticky_bit),
		.k_is_oob(k_is_oob),
		.non_zero_frac_field_size(non_zero_frac_field_size)
	);
	wire [N - 1:0] posit_encoded;
	posit_encoder #(
		.N(N),
		.ES(ES)
	) posit_encoder_inst(
		.is_zero_i(),
		.is_nar_i(),
		.sign(1'b0),
		.k(k),
		.exp(next_exp),
		.frac(frac),
		.posit(posit_encoded)
	);
	wire [N - 1:0] posit_pre_sign;
	round_posit #(.N(N)) round_posit_inst(
		.posit(posit_encoded),
		.round_bit(round_bit),
		.sticky_bit(sticky_bit),
		.k_is_oob(k_is_oob),
		.non_zero_frac_field_size(non_zero_frac_field_size),
		.posit_rounded(posit_pre_sign)
	);
	set_sign #(.N(N)) set_sign_inst(
		.posit_in(posit_pre_sign),
		.sign(sign),
		.posit_out(posit_o)
	);
endmodule
module fir_to_fixed (
	fir_i,
	fixed_o
);
	parameter N = -1;
	parameter FIR_TE_SIZE = -1;
	parameter FIR_FRAC_SIZE = -1;
	parameter FX_M = -1;
	parameter FX_B = -1;
	input wire [((1 + FIR_TE_SIZE) + FIR_FRAC_SIZE) - 1:0] fir_i;
	output wire [FX_B - 1:0] fixed_o;
	wire fir_sign;
	wire signed [FIR_TE_SIZE - 1:0] fir_te;
	wire [FIR_FRAC_SIZE - 1:0] fir_frac;
	assign {fir_sign, fir_te, fir_frac} = fir_i;
	wire [FX_B - 1:0] fixed_tmp;
	localparam MANT_MAX_LEN = N - 3;
	assign fixed_tmp = fir_frac << ((FX_B - FX_M) - (MANT_MAX_LEN + 1));
	wire fir_te_sign;
	assign fir_te_sign = fir_te >= 0;
	wire [63:0] fixed_signless;
	assign fixed_signless = (fir_te >= 0 ? fixed_tmp << fir_te : fixed_tmp >> -fir_te);
	assign fixed_o = (fir_sign == 1'b0 ? fixed_signless : ~fixed_signless + 1'b1);
endmodule
module fixed_to_fir (
	fixed_i,
	fir_o
);
	parameter N = -1;
	parameter FIR_TE_SIZE = -1;
	parameter FIR_FRAC_SIZE = -1;
	parameter FX_M = -1;
	parameter FX_B = -1;
	input wire [FX_B - 1:0] fixed_i;
	output wire [((1 + FIR_TE_SIZE) + FIR_FRAC_SIZE) - 1:0] fir_o;
	wire fir_sign;
	wire signed [FIR_TE_SIZE - 1:0] fir_te;
	wire [FIR_FRAC_SIZE - 1:0] fir_frac;
	wire [$clog2(FX_B - 1) - 1:0] lzc_fixed;
	wire lzc_valid;
	wire fixed_i_sign;
	assign fixed_i_sign = fixed_i[FX_B - 1];
	wire [FX_B - 1:0] fixed_i_abs;
	assign fixed_i_abs = (fixed_i_sign == 1'b0 ? fixed_i : ~fixed_i + 1'b1);
	lzc #(.NUM_BITS(FX_B)) lzc_inst(
		.bits_i(fixed_i_abs),
		.lzc_o(lzc_fixed),
		.valid_o(lzc_valid)
	);
	assign fir_sign = fixed_i_sign;
	assign fir_te = FX_M - lzc_fixed;
	localparam MANT_MAX_LEN = N - 3;
	wire [FX_B - 1:0] fixed_i_abs_corrected;
	assign fixed_i_abs_corrected = (fir_te >= 0 ? fixed_i_abs >> fir_te : fixed_i_abs << -fir_te);
	wire [(FX_B - FX_M) - 2:0] fixed_i_abs_corrected_frac_only;
	assign fixed_i_abs_corrected_frac_only = fixed_i_abs_corrected;
	localparam FX_N = (FX_B - FX_M) - 1;
	generate
		if (FIR_FRAC_SIZE <= FX_N) begin : genblk1
			assign fir_frac = fixed_i_abs_corrected[(1 + FX_N) - 1:0] >> (FX_N - FIR_FRAC_SIZE);
		end
		else begin : genblk1
			assign fir_frac = fixed_i_abs_corrected[(1 + FX_N) - 1:0] << (FIR_FRAC_SIZE - FX_N);
		end
	endgenerate
	assign fir_o = {fir_sign, fir_te, fir_frac};
endmodule
module zeroriscy_alu (
	operator_i,
	operand_a_i,
	operand_b_i,
	multdiv_operand_a_i,
	multdiv_operand_b_i,
	multdiv_en_i,
	adder_result_o,
	adder_result_ext_o,
	result_o,
	comparison_result_o,
	is_equal_result_o
);
	reg _sv2v_0;
	localparam zeroriscy_defines_ALU_OP_WIDTH = 6;
	input wire [5:0] operator_i;
	input wire [31:0] operand_a_i;
	input wire [31:0] operand_b_i;
	input wire [32:0] multdiv_operand_a_i;
	input wire [32:0] multdiv_operand_b_i;
	input wire multdiv_en_i;
	output wire [31:0] adder_result_o;
	output wire [33:0] adder_result_ext_o;
	output reg [31:0] result_o;
	output wire comparison_result_o;
	output wire is_equal_result_o;
	wire [31:0] operand_a_rev;
	wire [32:0] operand_b_neg;
	genvar _gv_k_1;
	generate
		for (_gv_k_1 = 0; _gv_k_1 < 32; _gv_k_1 = _gv_k_1 + 1) begin : g_revloop
			localparam k = _gv_k_1;
			assign operand_a_rev[k] = operand_a_i[31 - k];
		end
	endgenerate
	reg adder_op_b_negate;
	wire [32:0] adder_in_a;
	wire [32:0] adder_in_b;
	wire [31:0] adder_result;
	localparam zeroriscy_defines_ALU_EQ = 6'b001100;
	localparam zeroriscy_defines_ALU_GES = 6'b001010;
	localparam zeroriscy_defines_ALU_GEU = 6'b001011;
	localparam zeroriscy_defines_ALU_GTS = 6'b001000;
	localparam zeroriscy_defines_ALU_GTU = 6'b001001;
	localparam zeroriscy_defines_ALU_LES = 6'b000100;
	localparam zeroriscy_defines_ALU_LEU = 6'b000101;
	localparam zeroriscy_defines_ALU_LTS = 6'b000000;
	localparam zeroriscy_defines_ALU_LTU = 6'b000001;
	localparam zeroriscy_defines_ALU_NE = 6'b001101;
	localparam zeroriscy_defines_ALU_SLETS = 6'b000110;
	localparam zeroriscy_defines_ALU_SLETU = 6'b000111;
	localparam zeroriscy_defines_ALU_SLTS = 6'b000010;
	localparam zeroriscy_defines_ALU_SLTU = 6'b000011;
	localparam zeroriscy_defines_ALU_SUB = 6'b011001;
	always @(*) begin
		if (_sv2v_0)
			;
		adder_op_b_negate = 1'b0;
		(* full_case, parallel_case *)
		case (operator_i)
			zeroriscy_defines_ALU_SUB, zeroriscy_defines_ALU_EQ, zeroriscy_defines_ALU_NE, zeroriscy_defines_ALU_GTU, zeroriscy_defines_ALU_GEU, zeroriscy_defines_ALU_LTU, zeroriscy_defines_ALU_LEU, zeroriscy_defines_ALU_GTS, zeroriscy_defines_ALU_GES, zeroriscy_defines_ALU_LTS, zeroriscy_defines_ALU_LES, zeroriscy_defines_ALU_SLTS, zeroriscy_defines_ALU_SLTU, zeroriscy_defines_ALU_SLETS, zeroriscy_defines_ALU_SLETU: adder_op_b_negate = 1'b1;
			default:
				;
		endcase
	end
	assign adder_in_a = (multdiv_en_i ? multdiv_operand_a_i : {operand_a_i, 1'b1});
	assign operand_b_neg = {operand_b_i, 1'b0} ^ {33 {adder_op_b_negate}};
	assign adder_in_b = (multdiv_en_i ? multdiv_operand_b_i : operand_b_neg);
	assign adder_result_ext_o = $unsigned(adder_in_a) + $unsigned(adder_in_b);
	assign adder_result = adder_result_ext_o[32:1];
	assign adder_result_o = adder_result;
	wire shift_left;
	wire shift_arithmetic;
	wire [31:0] shift_amt;
	wire [31:0] shift_op_a;
	wire [31:0] shift_result;
	wire [31:0] shift_right_result;
	wire [31:0] shift_left_result;
	assign shift_amt = operand_b_i;
	localparam zeroriscy_defines_ALU_SLL = 6'b100111;
	assign shift_left = operator_i == zeroriscy_defines_ALU_SLL;
	localparam zeroriscy_defines_ALU_SRA = 6'b100100;
	assign shift_arithmetic = operator_i == zeroriscy_defines_ALU_SRA;
	assign shift_op_a = (shift_left ? operand_a_rev : operand_a_i);
	wire [32:0] shift_op_a_32;
	assign shift_op_a_32 = {shift_arithmetic & shift_op_a[31], shift_op_a};
	assign shift_right_result = $signed(shift_op_a_32) >>> shift_amt[4:0];
	genvar _gv_j_1;
	generate
		for (_gv_j_1 = 0; _gv_j_1 < 32; _gv_j_1 = _gv_j_1 + 1) begin : g_resrevloop
			localparam j = _gv_j_1;
			assign shift_left_result[j] = shift_right_result[31 - j];
		end
	endgenerate
	assign shift_result = (shift_left ? shift_left_result : shift_right_result);
	wire is_equal;
	reg is_greater_equal;
	reg cmp_signed;
	always @(*) begin
		if (_sv2v_0)
			;
		cmp_signed = 1'b0;
		(* full_case, parallel_case *)
		case (operator_i)
			zeroriscy_defines_ALU_GTS, zeroriscy_defines_ALU_GES, zeroriscy_defines_ALU_LTS, zeroriscy_defines_ALU_LES, zeroriscy_defines_ALU_SLTS, zeroriscy_defines_ALU_SLETS: cmp_signed = 1'b1;
			default:
				;
		endcase
	end
	assign is_equal = adder_result == 32'b00000000000000000000000000000000;
	assign is_equal_result_o = is_equal;
	always @(*) begin
		if (_sv2v_0)
			;
		if ((operand_a_i[31] ^ operand_b_i[31]) == 0)
			is_greater_equal = adder_result[31] == 0;
		else
			is_greater_equal = operand_a_i[31] ^ cmp_signed;
	end
	reg cmp_result;
	always @(*) begin
		if (_sv2v_0)
			;
		cmp_result = is_equal;
		(* full_case, parallel_case *)
		case (operator_i)
			zeroriscy_defines_ALU_EQ: cmp_result = is_equal;
			zeroriscy_defines_ALU_NE: cmp_result = ~is_equal;
			zeroriscy_defines_ALU_GTS, zeroriscy_defines_ALU_GTU: cmp_result = is_greater_equal && ~is_equal;
			zeroriscy_defines_ALU_GES, zeroriscy_defines_ALU_GEU: cmp_result = is_greater_equal;
			zeroriscy_defines_ALU_LTS, zeroriscy_defines_ALU_SLTS, zeroriscy_defines_ALU_LTU, zeroriscy_defines_ALU_SLTU: cmp_result = ~is_greater_equal;
			zeroriscy_defines_ALU_SLETS, zeroriscy_defines_ALU_SLETU, zeroriscy_defines_ALU_LES, zeroriscy_defines_ALU_LEU: cmp_result = ~is_greater_equal || is_equal;
			default:
				;
		endcase
	end
	assign comparison_result_o = cmp_result;
	localparam zeroriscy_defines_ALU_ADD = 6'b011000;
	localparam zeroriscy_defines_ALU_AND = 6'b010101;
	localparam zeroriscy_defines_ALU_OR = 6'b101110;
	localparam zeroriscy_defines_ALU_SRL = 6'b100101;
	localparam zeroriscy_defines_ALU_XOR = 6'b101111;
	always @(*) begin
		if (_sv2v_0)
			;
		result_o = 1'sb0;
		(* full_case, parallel_case *)
		case (operator_i)
			zeroriscy_defines_ALU_AND: result_o = operand_a_i & operand_b_i;
			zeroriscy_defines_ALU_OR: result_o = operand_a_i | operand_b_i;
			zeroriscy_defines_ALU_XOR: result_o = operand_a_i ^ operand_b_i;
			zeroriscy_defines_ALU_ADD, zeroriscy_defines_ALU_SUB: result_o = adder_result;
			zeroriscy_defines_ALU_SLL, zeroriscy_defines_ALU_SRL, zeroriscy_defines_ALU_SRA: result_o = shift_result;
			zeroriscy_defines_ALU_EQ, zeroriscy_defines_ALU_NE, zeroriscy_defines_ALU_GTU, zeroriscy_defines_ALU_GEU, zeroriscy_defines_ALU_LTU, zeroriscy_defines_ALU_LEU, zeroriscy_defines_ALU_GTS, zeroriscy_defines_ALU_GES, zeroriscy_defines_ALU_LTS, zeroriscy_defines_ALU_LES, zeroriscy_defines_ALU_SLTS, zeroriscy_defines_ALU_SLTU, zeroriscy_defines_ALU_SLETS, zeroriscy_defines_ALU_SLETU: result_o = cmp_result;
			default:
				;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_compressed_decoder (
	instr_i,
	instr_o,
	is_compressed_o,
	illegal_instr_o
);
	reg _sv2v_0;
	input wire [31:0] instr_i;
	output reg [31:0] instr_o;
	output wire is_compressed_o;
	output reg illegal_instr_o;
	localparam zeroriscy_defines_OPCODE_BRANCH = 7'h63;
	localparam zeroriscy_defines_OPCODE_JAL = 7'h6f;
	localparam zeroriscy_defines_OPCODE_JALR = 7'h67;
	localparam zeroriscy_defines_OPCODE_LOAD = 7'h03;
	localparam zeroriscy_defines_OPCODE_LUI = 7'h37;
	localparam zeroriscy_defines_OPCODE_OP = 7'h33;
	localparam zeroriscy_defines_OPCODE_OPIMM = 7'h13;
	localparam zeroriscy_defines_OPCODE_STORE = 7'h23;
	always @(*) begin
		if (_sv2v_0)
			;
		illegal_instr_o = 1'b0;
		instr_o = 1'sb0;
		(* full_case, parallel_case *)
		case (instr_i[1:0])
			2'b00:
				(* full_case, parallel_case *)
				case (instr_i[15:13])
					3'b000: begin
						instr_o = {2'b00, instr_i[10:7], instr_i[12:11], instr_i[5], instr_i[6], 12'h041, instr_i[4:2], zeroriscy_defines_OPCODE_OPIMM};
						if (instr_i[12:5] == 8'b00000000)
							illegal_instr_o = 1'b1;
					end
					3'b010: instr_o = {5'b00000, instr_i[5], instr_i[12:10], instr_i[6], 4'b0001, instr_i[9:7], 5'b01001, instr_i[4:2], zeroriscy_defines_OPCODE_LOAD};
					3'b110: instr_o = {5'b00000, instr_i[5], instr_i[12], 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b010, instr_i[11:10], instr_i[6], 2'b00, zeroriscy_defines_OPCODE_STORE};
					default: illegal_instr_o = 1'b1;
				endcase
			2'b01:
				(* full_case, parallel_case *)
				case (instr_i[15:13])
					3'b000: instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], instr_i[11:7], 3'b000, instr_i[11:7], zeroriscy_defines_OPCODE_OPIMM};
					3'b001, 3'b101: instr_o = {instr_i[12], instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], {9 {instr_i[12]}}, 4'b0000, ~instr_i[15], zeroriscy_defines_OPCODE_JAL};
					3'b010: begin
						instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 8'b00000000, instr_i[11:7], zeroriscy_defines_OPCODE_OPIMM};
						if (instr_i[11:7] == 5'b00000)
							illegal_instr_o = 1'b1;
					end
					3'b011: begin
						instr_o = {{15 {instr_i[12]}}, instr_i[6:2], instr_i[11:7], zeroriscy_defines_OPCODE_LUI};
						if (instr_i[11:7] == 5'h02)
							instr_o = {{3 {instr_i[12]}}, instr_i[4:3], instr_i[5], instr_i[2], instr_i[6], 17'h00202, zeroriscy_defines_OPCODE_OPIMM};
						else if (instr_i[11:7] == 5'b00000)
							illegal_instr_o = 1'b1;
						if ({instr_i[12], instr_i[6:2]} == 6'b000000)
							illegal_instr_o = 1'b1;
					end
					3'b100:
						(* full_case, parallel_case *)
						case (instr_i[11:10])
							2'b00, 2'b01: begin
								instr_o = {1'b0, instr_i[10], 5'b00000, instr_i[6:2], 2'b01, instr_i[9:7], 5'b10101, instr_i[9:7], zeroriscy_defines_OPCODE_OPIMM};
								if (instr_i[12] == 1'b1)
									illegal_instr_o = 1'b1;
								if (instr_i[6:2] == 5'b00000)
									illegal_instr_o = 1'b1;
							end
							2'b10: instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 2'b01, instr_i[9:7], 5'b11101, instr_i[9:7], zeroriscy_defines_OPCODE_OPIMM};
							2'b11:
								(* full_case, parallel_case *)
								case ({instr_i[12], instr_i[6:5]})
									3'b000: instr_o = {9'b010000001, instr_i[4:2], 2'b01, instr_i[9:7], 5'b00001, instr_i[9:7], zeroriscy_defines_OPCODE_OP};
									3'b001: instr_o = {9'b000000001, instr_i[4:2], 2'b01, instr_i[9:7], 5'b10001, instr_i[9:7], zeroriscy_defines_OPCODE_OP};
									3'b010: instr_o = {9'b000000001, instr_i[4:2], 2'b01, instr_i[9:7], 5'b11001, instr_i[9:7], zeroriscy_defines_OPCODE_OP};
									3'b011: instr_o = {9'b000000001, instr_i[4:2], 2'b01, instr_i[9:7], 5'b11101, instr_i[9:7], zeroriscy_defines_OPCODE_OP};
									3'b100, 3'b101, 3'b110, 3'b111: illegal_instr_o = 1'b1;
								endcase
						endcase
					3'b110, 3'b111: instr_o = {{4 {instr_i[12]}}, instr_i[6:5], instr_i[2], 7'b0000001, instr_i[9:7], 2'b00, instr_i[13], instr_i[11:10], instr_i[4:3], instr_i[12], zeroriscy_defines_OPCODE_BRANCH};
					default: illegal_instr_o = 1'b1;
				endcase
			2'b10:
				(* full_case, parallel_case *)
				case (instr_i[15:13])
					3'b000: begin
						instr_o = {7'b0000000, instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], zeroriscy_defines_OPCODE_OPIMM};
						if (instr_i[11:7] == 5'b00000)
							illegal_instr_o = 1'b1;
						if ((instr_i[12] == 1'b1) || (instr_i[6:2] == 5'b00000))
							illegal_instr_o = 1'b1;
					end
					3'b010: begin
						instr_o = {4'b0000, instr_i[3:2], instr_i[12], instr_i[6:4], 10'h012, instr_i[11:7], zeroriscy_defines_OPCODE_LOAD};
						if (instr_i[11:7] == 5'b00000)
							illegal_instr_o = 1'b1;
					end
					3'b100:
						if (instr_i[12] == 1'b0) begin
							instr_o = {7'b0000000, instr_i[6:2], 8'b00000000, instr_i[11:7], zeroriscy_defines_OPCODE_OP};
							if (instr_i[6:2] == 5'b00000)
								instr_o = {12'b000000000000, instr_i[11:7], 8'b00000000, zeroriscy_defines_OPCODE_JALR};
						end
						else begin
							instr_o = {7'b0000000, instr_i[6:2], instr_i[11:7], 3'b000, instr_i[11:7], zeroriscy_defines_OPCODE_OP};
							if (instr_i[11:7] == 5'b00000) begin
								instr_o = 32'h00100073;
								if (instr_i[6:2] != 5'b00000)
									illegal_instr_o = 1'b1;
							end
							else if (instr_i[6:2] == 5'b00000)
								instr_o = {12'b000000000000, instr_i[11:7], 8'b00000001, zeroriscy_defines_OPCODE_JALR};
						end
					3'b110: instr_o = {4'b0000, instr_i[8:7], instr_i[12], instr_i[6:2], 8'h12, instr_i[11:9], 2'b00, zeroriscy_defines_OPCODE_STORE};
					default: illegal_instr_o = 1'b1;
				endcase
			default: instr_o = instr_i;
		endcase
	end
	assign is_compressed_o = instr_i[1:0] != 2'b11;
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_controller (
	clk,
	rst_n,
	fetch_enable_i,
	ctrl_busy_o,
	first_fetch_o,
	is_decoding_o,
	deassert_we_o,
	illegal_insn_i,
	ecall_insn_i,
	mret_insn_i,
	pipe_flush_i,
	ebrk_insn_i,
	csr_status_i,
	instr_valid_i,
	instr_req_o,
	pc_set_o,
	pc_mux_o,
	exc_pc_mux_o,
	data_misaligned_i,
	branch_in_id_i,
	branch_taken_ex_i,
	branch_set_i,
	jump_set_i,
	instr_multicyle_i,
	irq_req_ctrl_i,
	irq_id_ctrl_i,
	m_IE_i,
	irq_ack_o,
	irq_id_o,
	exc_cause_o,
	exc_ack_o,
	exc_kill_o,
	csr_save_if_o,
	csr_save_id_o,
	csr_cause_o,
	csr_restore_mret_id_o,
	csr_save_cause_o,
	dbg_req_i,
	dbg_ack_o,
	dbg_stall_i,
	dbg_jump_req_i,
	dbg_settings_i,
	dbg_trap_o,
	operand_a_fw_mux_sel_o,
	halt_if_o,
	halt_id_o,
	id_ready_i,
	perf_jump_o,
	perf_tbranch_o
);
	reg _sv2v_0;
	parameter REG_ADDR_WIDTH = 5;
	input wire clk;
	input wire rst_n;
	input wire fetch_enable_i;
	output reg ctrl_busy_o;
	output reg first_fetch_o;
	output reg is_decoding_o;
	output reg deassert_we_o;
	input wire illegal_insn_i;
	input wire ecall_insn_i;
	input wire mret_insn_i;
	input wire pipe_flush_i;
	input wire ebrk_insn_i;
	input wire csr_status_i;
	input wire instr_valid_i;
	output reg instr_req_o;
	output reg pc_set_o;
	output reg [2:0] pc_mux_o;
	output reg [1:0] exc_pc_mux_o;
	input wire data_misaligned_i;
	input wire branch_in_id_i;
	input wire branch_taken_ex_i;
	input wire branch_set_i;
	input wire jump_set_i;
	input wire instr_multicyle_i;
	input wire irq_req_ctrl_i;
	input wire [4:0] irq_id_ctrl_i;
	input wire m_IE_i;
	output reg irq_ack_o;
	output reg [4:0] irq_id_o;
	output reg [5:0] exc_cause_o;
	output reg exc_ack_o;
	output reg exc_kill_o;
	output reg csr_save_if_o;
	output reg csr_save_id_o;
	output reg [5:0] csr_cause_o;
	output reg csr_restore_mret_id_o;
	output reg csr_save_cause_o;
	input wire dbg_req_i;
	output reg dbg_ack_o;
	input wire dbg_stall_i;
	input wire dbg_jump_req_i;
	localparam zeroriscy_defines_DBG_SETS_W = 6;
	input wire [5:0] dbg_settings_i;
	output reg dbg_trap_o;
	output wire [1:0] operand_a_fw_mux_sel_o;
	output reg halt_if_o;
	output reg halt_id_o;
	input wire id_ready_i;
	output reg perf_jump_o;
	output reg perf_tbranch_o;
	reg [3:0] ctrl_fsm_cs;
	reg [3:0] ctrl_fsm_ns;
	reg irq_enable_int;
	always @(negedge clk)
		if (is_decoding_o && illegal_insn_i)
			$display("%t: Illegal instruction (core %0d) at PC 0x%h:", $time, zeroriscy_core.core_id_i, zeroriscy_id_stage.pc_id_i);
	localparam zeroriscy_defines_DBG_SETS_EBRK = 1;
	localparam zeroriscy_defines_DBG_SETS_ECALL = 4;
	localparam zeroriscy_defines_DBG_SETS_EILL = 3;
	localparam zeroriscy_defines_DBG_SETS_SSTE = 0;
	localparam zeroriscy_defines_EXC_CAUSE_BREAKPOINT = 6'h03;
	localparam zeroriscy_defines_EXC_CAUSE_ECALL_MMODE = 6'h0b;
	localparam zeroriscy_defines_EXC_CAUSE_ILLEGAL_INSN = 6'h02;
	localparam zeroriscy_defines_EXC_PC_ECALL = 2'b01;
	localparam zeroriscy_defines_EXC_PC_ILLINSN = 2'b00;
	localparam zeroriscy_defines_EXC_PC_IRQ = 2'b11;
	localparam zeroriscy_defines_PC_BOOT = 3'b000;
	localparam zeroriscy_defines_PC_DBG_NPC = 3'b111;
	localparam zeroriscy_defines_PC_ERET = 3'b101;
	localparam zeroriscy_defines_PC_EXCEPTION = 3'b100;
	localparam zeroriscy_defines_PC_JUMP = 3'b010;
	always @(*) begin
		if (_sv2v_0)
			;
		instr_req_o = 1'b1;
		exc_ack_o = 1'b0;
		exc_kill_o = 1'b0;
		csr_save_if_o = 1'b0;
		csr_save_id_o = 1'b0;
		csr_restore_mret_id_o = 1'b0;
		csr_save_cause_o = 1'b0;
		exc_cause_o = 1'sb0;
		exc_pc_mux_o = zeroriscy_defines_EXC_PC_IRQ;
		csr_cause_o = 1'sb0;
		pc_mux_o = zeroriscy_defines_PC_BOOT;
		pc_set_o = 1'b0;
		ctrl_fsm_ns = ctrl_fsm_cs;
		ctrl_busy_o = 1'b1;
		is_decoding_o = 1'b0;
		first_fetch_o = 1'b0;
		halt_if_o = 1'b0;
		halt_id_o = 1'b0;
		dbg_ack_o = 1'b0;
		irq_ack_o = 1'b0;
		irq_id_o = irq_id_ctrl_i;
		irq_enable_int = m_IE_i;
		dbg_trap_o = 1'b0;
		perf_tbranch_o = 1'b0;
		perf_jump_o = 1'b0;
		(* full_case, parallel_case *)
		case (ctrl_fsm_cs)
			4'd0: begin
				ctrl_busy_o = 1'b0;
				instr_req_o = 1'b0;
				if (fetch_enable_i == 1'b1)
					ctrl_fsm_ns = 4'd1;
				else if (dbg_req_i)
					ctrl_fsm_ns = 4'd8;
			end
			4'd1: begin
				instr_req_o = 1'b1;
				pc_mux_o = zeroriscy_defines_PC_BOOT;
				pc_set_o = 1'b1;
				ctrl_fsm_ns = 4'd4;
			end
			4'd2: begin
				ctrl_busy_o = 1'b0;
				instr_req_o = 1'b0;
				halt_if_o = 1'b1;
				halt_id_o = 1'b1;
				ctrl_fsm_ns = 4'd3;
			end
			4'd3: begin
				ctrl_busy_o = 1'b0;
				instr_req_o = 1'b0;
				halt_if_o = 1'b1;
				halt_id_o = 1'b1;
				dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
				if (dbg_req_i) begin
					if (fetch_enable_i || irq_req_ctrl_i)
						ctrl_fsm_ns = 4'd8;
					else
						ctrl_fsm_ns = 4'd9;
				end
				else if (fetch_enable_i || irq_req_ctrl_i)
					ctrl_fsm_ns = 4'd4;
			end
			4'd4: begin
				first_fetch_o = 1'b1;
				if ((id_ready_i == 1'b1) && (dbg_stall_i == 1'b0))
					ctrl_fsm_ns = 4'd5;
				if (irq_req_ctrl_i & irq_enable_int) begin
					ctrl_fsm_ns = 4'd7;
					halt_if_o = 1'b1;
					halt_id_o = 1'b1;
				end
			end
			4'd5: begin
				is_decoding_o = 1'b0;
				if (instr_valid_i) begin
					is_decoding_o = 1'b1;
					(* full_case, parallel_case *)
					case (1'b1)
						branch_set_i: begin
							pc_mux_o = zeroriscy_defines_PC_JUMP;
							pc_set_o = 1'b1;
							perf_tbranch_o = 1'b1;
							dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
							if (dbg_req_i)
								ctrl_fsm_ns = 4'd8;
						end
						jump_set_i: begin
							pc_mux_o = zeroriscy_defines_PC_JUMP;
							pc_set_o = 1'b1;
							perf_jump_o = 1'b1;
							dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
						end
						((((mret_insn_i | ecall_insn_i) | pipe_flush_i) | ebrk_insn_i) | illegal_insn_i) | csr_status_i: begin
							ctrl_fsm_ns = 4'd6;
							halt_if_o = 1'b1;
							halt_id_o = 1'b1;
						end
						default: begin
							dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
							(* full_case, parallel_case *)
							case (1'b1)
								((irq_req_ctrl_i & irq_enable_int) & ~instr_multicyle_i) & ~branch_in_id_i: begin
									ctrl_fsm_ns = 4'd7;
									halt_if_o = 1'b1;
									halt_id_o = 1'b1;
								end
								dbg_req_i & ~branch_taken_ex_i: begin
									halt_if_o = 1'b1;
									if (id_ready_i)
										ctrl_fsm_ns = 4'd8;
								end
								default: exc_kill_o = ((irq_req_ctrl_i & ~instr_multicyle_i) & ~branch_in_id_i ? 1'b1 : 1'b0);
							endcase
						end
					endcase
				end
				else if (irq_req_ctrl_i & irq_enable_int) begin
					ctrl_fsm_ns = 4'd7;
					halt_if_o = 1'b1;
					halt_id_o = 1'b1;
				end
			end
			4'd8: begin
				dbg_ack_o = 1'b1;
				halt_if_o = 1'b1;
				ctrl_fsm_ns = 4'd10;
			end
			4'd9: begin
				dbg_ack_o = 1'b1;
				halt_if_o = 1'b1;
				ctrl_fsm_ns = 4'd12;
			end
			4'd12: begin
				halt_if_o = 1'b1;
				if (dbg_jump_req_i) begin
					pc_mux_o = zeroriscy_defines_PC_DBG_NPC;
					pc_set_o = 1'b1;
					ctrl_fsm_ns = 4'd10;
				end
				if (dbg_stall_i == 1'b0)
					ctrl_fsm_ns = 4'd3;
			end
			4'd10: begin
				halt_if_o = 1'b1;
				if (dbg_jump_req_i) begin
					pc_mux_o = zeroriscy_defines_PC_DBG_NPC;
					pc_set_o = 1'b1;
					ctrl_fsm_ns = 4'd10;
				end
				if (dbg_stall_i == 1'b0)
					ctrl_fsm_ns = 4'd5;
			end
			4'd7: begin
				pc_mux_o = zeroriscy_defines_PC_EXCEPTION;
				pc_set_o = 1'b1;
				exc_pc_mux_o = zeroriscy_defines_EXC_PC_IRQ;
				exc_cause_o = {1'b0, irq_id_ctrl_i};
				csr_save_cause_o = 1'b1;
				csr_cause_o = {1'b1, irq_id_ctrl_i};
				csr_save_if_o = 1'b1;
				irq_ack_o = 1'b1;
				exc_ack_o = 1'b1;
				ctrl_fsm_ns = 4'd5;
			end
			4'd6: begin
				halt_if_o = (fetch_enable_i ? dbg_req_i : 1'b1);
				halt_id_o = 1'b1;
				ctrl_fsm_ns = (dbg_req_i ? 4'd8 : 4'd5);
				(* full_case, parallel_case *)
				case (1'b1)
					ecall_insn_i: begin
						pc_mux_o = zeroriscy_defines_PC_EXCEPTION;
						pc_set_o = 1'b1;
						csr_save_id_o = 1'b1;
						csr_save_cause_o = 1'b1;
						exc_pc_mux_o = zeroriscy_defines_EXC_PC_ECALL;
						exc_cause_o = zeroriscy_defines_EXC_CAUSE_ECALL_MMODE;
						csr_cause_o = zeroriscy_defines_EXC_CAUSE_ECALL_MMODE;
						dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_ECALL] | dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
					end
					illegal_insn_i: begin
						pc_mux_o = zeroriscy_defines_PC_EXCEPTION;
						pc_set_o = 1'b1;
						csr_save_id_o = 1'b1;
						csr_save_cause_o = 1'b1;
						exc_pc_mux_o = zeroriscy_defines_EXC_PC_ILLINSN;
						exc_cause_o = zeroriscy_defines_EXC_CAUSE_ILLEGAL_INSN;
						csr_cause_o = zeroriscy_defines_EXC_CAUSE_ILLEGAL_INSN;
						dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_EILL] | dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
					end
					mret_insn_i: begin
						pc_mux_o = zeroriscy_defines_PC_ERET;
						pc_set_o = 1'b1;
						csr_restore_mret_id_o = 1'b1;
						dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
					end
					ebrk_insn_i: begin
						dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_EBRK] | dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
						exc_cause_o = zeroriscy_defines_EXC_CAUSE_BREAKPOINT;
					end
					csr_status_i: dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
					pipe_flush_i: dbg_trap_o = dbg_settings_i[zeroriscy_defines_DBG_SETS_SSTE];
					default:
						;
				endcase
				if (fetch_enable_i) begin
					if (dbg_req_i)
						ctrl_fsm_ns = 4'd8;
					else
						ctrl_fsm_ns = 4'd5;
				end
				else if (dbg_req_i)
					ctrl_fsm_ns = 4'd9;
				else
					ctrl_fsm_ns = (mret_insn_i | pipe_flush_i ? 4'd2 : 4'd5);
			end
			default: begin
				instr_req_o = 1'b0;
				ctrl_fsm_ns = 4'd0;
			end
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		deassert_we_o = 1'b0;
		if (~is_decoding_o)
			deassert_we_o = 1'b1;
		if (illegal_insn_i)
			deassert_we_o = 1'b1;
	end
	localparam zeroriscy_defines_SEL_MISALIGNED = 2'b11;
	localparam zeroriscy_defines_SEL_REGFILE = 2'b00;
	assign operand_a_fw_mux_sel_o = (data_misaligned_i ? zeroriscy_defines_SEL_MISALIGNED : zeroriscy_defines_SEL_REGFILE);
	always @(posedge clk or negedge rst_n) begin : UPDATE_REGS
		if (rst_n == 1'b0)
			ctrl_fsm_cs <= 4'd0;
		else
			ctrl_fsm_cs <= ctrl_fsm_ns;
	end
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_core (
	clk_i,
	rst_ni,
	clock_en_i,
	test_en_i,
	core_id_i,
	cluster_id_i,
	boot_addr_i,
	instr_req_o,
	instr_gnt_i,
	instr_rvalid_i,
	instr_addr_o,
	instr_rdata_i,
	data_req_o,
	data_gnt_i,
	data_rvalid_i,
	data_we_o,
	data_be_o,
	data_addr_o,
	data_wdata_o,
	data_rdata_i,
	data_err_i,
	irq_i,
	irq_id_i,
	irq_ack_o,
	irq_id_o,
	debug_req_i,
	debug_gnt_o,
	debug_rvalid_o,
	debug_addr_i,
	debug_we_i,
	debug_wdata_i,
	debug_rdata_o,
	debug_halted_o,
	debug_halt_i,
	debug_resume_i,
	fetch_enable_i,
	core_busy_o,
	ext_perf_counters_i
);
	parameter N_EXT_PERF_COUNTERS = 0;
	parameter RV32E = 0;
	parameter RV32M = 1;
	input wire clk_i;
	input wire rst_ni;
	input wire clock_en_i;
	input wire test_en_i;
	input wire [3:0] core_id_i;
	input wire [5:0] cluster_id_i;
	input wire [31:0] boot_addr_i;
	output wire instr_req_o;
	input wire instr_gnt_i;
	input wire instr_rvalid_i;
	output wire [31:0] instr_addr_o;
	input wire [31:0] instr_rdata_i;
	output wire data_req_o;
	input wire data_gnt_i;
	input wire data_rvalid_i;
	output wire data_we_o;
	output wire [3:0] data_be_o;
	output wire [31:0] data_addr_o;
	output wire [31:0] data_wdata_o;
	input wire [31:0] data_rdata_i;
	input wire data_err_i;
	input wire irq_i;
	input wire [4:0] irq_id_i;
	output wire irq_ack_o;
	output wire [4:0] irq_id_o;
	input wire debug_req_i;
	output wire debug_gnt_o;
	output wire debug_rvalid_o;
	input wire [14:0] debug_addr_i;
	input wire debug_we_i;
	input wire [31:0] debug_wdata_i;
	output wire [31:0] debug_rdata_o;
	output wire debug_halted_o;
	input wire debug_halt_i;
	input wire debug_resume_i;
	input wire fetch_enable_i;
	output wire core_busy_o;
	input wire [N_EXT_PERF_COUNTERS - 1:0] ext_perf_counters_i;
	localparam N_HWLP = 2;
	localparam N_HWLP_BITS = 1;
	wire instr_valid_id;
	wire [31:0] instr_rdata_id;
	wire is_compressed_id;
	wire illegal_c_insn_id;
	wire [31:0] pc_if;
	wire [31:0] pc_id;
	wire clear_instr_valid;
	wire pc_set;
	wire [2:0] pc_mux_id;
	wire [1:0] exc_pc_mux_id;
	wire [5:0] exc_cause;
	wire lsu_load_err;
	wire lsu_store_err;
	wire is_decoding;
	wire data_misaligned;
	wire [31:0] misaligned_addr;
	wire [31:0] jump_target_ex;
	wire branch_in_ex;
	wire branch_decision;
	wire ctrl_busy;
	wire if_busy;
	wire lsu_busy;
	localparam zeroriscy_defines_ALU_OP_WIDTH = 6;
	wire [5:0] alu_operator_ex;
	wire [31:0] alu_operand_a_ex;
	wire [31:0] alu_operand_b_ex;
	wire [31:0] alu_adder_result_ex;
	wire [31:0] regfile_wdata_ex;
	wire ppu_en_ex;
	localparam zeroriscy_defines_PPU_OP_WIDTH = 3;
	wire [2:0] ppu_operator_ex;
	wire [31:0] ppu_operand_a_ex;
	wire [31:0] ppu_operand_b_ex;
	wire [31:0] ppu_operand_c_ex;
	wire [31:0] ppu_result_ex;
	wire mult_en_ex;
	wire div_en_ex;
	wire [1:0] multdiv_operator_ex;
	wire [1:0] multdiv_signed_mode_ex;
	wire [31:0] multdiv_operand_a_ex;
	wire [31:0] multdiv_operand_b_ex;
	wire csr_access_ex;
	wire [1:0] csr_op_ex;
	wire csr_access;
	wire [1:0] csr_op;
	wire [11:0] csr_addr;
	wire [11:0] csr_addr_int;
	wire [31:0] csr_rdata;
	wire [31:0] csr_wdata;
	wire data_we_ex;
	wire [1:0] data_type_ex;
	wire data_sign_ext_ex;
	wire [1:0] data_reg_offset_ex;
	wire data_req_ex;
	wire [31:0] data_wdata_ex;
	wire data_load_event_ex;
	wire data_misaligned_ex;
	wire [31:0] regfile_wdata_lsu;
	wire halt_if;
	wire id_ready;
	wire ex_ready;
	wire if_valid;
	wire id_valid;
	wire wb_valid;
	wire lsu_ready_ex;
	wire data_valid_lsu;
	wire instr_req_int;
	wire m_irq_enable;
	wire [31:0] mepc;
	wire csr_save_cause;
	wire csr_save_if;
	wire csr_save_id;
	wire [5:0] csr_cause;
	wire csr_restore_mret_id;
	wire csr_restore_uret_id;
	localparam zeroriscy_defines_DBG_SETS_W = 6;
	wire [5:0] dbg_settings;
	wire dbg_req;
	wire dbg_ack;
	wire dbg_stall;
	wire dbg_trap;
	wire dbg_reg_rreq;
	wire [4:0] dbg_reg_raddr;
	wire [31:0] dbg_reg_rdata;
	wire dbg_reg_wreq;
	wire [4:0] dbg_reg_waddr;
	wire [31:0] dbg_reg_wdata;
	wire dbg_csr_req;
	wire [11:0] dbg_csr_addr;
	wire dbg_csr_we;
	wire [31:0] dbg_csr_wdata;
	wire [31:0] dbg_jump_addr;
	wire dbg_jump_req;
	wire perf_imiss;
	wire perf_jump;
	wire perf_branch;
	wire perf_tbranch;
	wire core_ctrl_firstfetch;
	wire core_busy_int;
	reg core_busy_q;
	wire clk;
	wire clock_en;
	wire dbg_busy;
	wire sleeping;
	assign core_busy_int = (data_load_event_ex & data_req_o ? if_busy : (if_busy | ctrl_busy) | lsu_busy);
	always @(posedge clk or negedge rst_ni)
		if (rst_ni == 1'b0)
			core_busy_q <= 1'b0;
		else
			core_busy_q <= core_busy_int;
	assign core_busy_o = (core_ctrl_firstfetch ? 1'b1 : core_busy_q);
	assign dbg_busy = (((dbg_req | dbg_csr_req) | dbg_jump_req) | dbg_reg_wreq) | debug_req_i;
	assign clock_en = (clock_en_i | core_busy_o) | dbg_busy;
	assign sleeping = ~fetch_enable_i & ~core_busy_o;
	cluster_clock_gating core_clock_gate_i(
		.clk_i(clk_i),
		.en_i(clock_en),
		.test_en_i(test_en_i),
		.clk_o(clk)
	);
	zeroriscy_if_stage if_stage_i(
		.clk(clk),
		.rst_n(rst_ni),
		.boot_addr_i(boot_addr_i),
		.req_i(instr_req_int),
		.instr_req_o(instr_req_o),
		.instr_addr_o(instr_addr_o),
		.instr_gnt_i(instr_gnt_i),
		.instr_rvalid_i(instr_rvalid_i),
		.instr_rdata_i(instr_rdata_i),
		.instr_valid_id_o(instr_valid_id),
		.instr_rdata_id_o(instr_rdata_id),
		.is_compressed_id_o(is_compressed_id),
		.illegal_c_insn_id_o(illegal_c_insn_id),
		.pc_if_o(pc_if),
		.pc_id_o(pc_id),
		.clear_instr_valid_i(clear_instr_valid),
		.pc_set_i(pc_set),
		.exception_pc_reg_i(mepc),
		.pc_mux_i(pc_mux_id),
		.exc_pc_mux_i(exc_pc_mux_id),
		.exc_vec_pc_mux_i(exc_cause[4:0]),
		.dbg_jump_addr_i(dbg_jump_addr),
		.jump_target_ex_i(jump_target_ex),
		.halt_if_i(halt_if),
		.id_ready_i(id_ready),
		.if_valid_o(if_valid),
		.if_busy_o(if_busy),
		.perf_imiss_o(perf_imiss)
	);
	zeroriscy_id_stage #(
		.RV32E(RV32E),
		.RV32M(RV32M)
	) id_stage_i(
		.clk(clk),
		.rst_n(rst_ni),
		.test_en_i(test_en_i),
		.fetch_enable_i(fetch_enable_i),
		.ctrl_busy_o(ctrl_busy),
		.core_ctrl_firstfetch_o(core_ctrl_firstfetch),
		.is_decoding_o(is_decoding),
		.instr_valid_i(instr_valid_id),
		.instr_rdata_i(instr_rdata_id),
		.instr_req_o(instr_req_int),
		.branch_in_ex_o(branch_in_ex),
		.branch_decision_i(branch_decision),
		.clear_instr_valid_o(clear_instr_valid),
		.pc_set_o(pc_set),
		.pc_mux_o(pc_mux_id),
		.exc_pc_mux_o(exc_pc_mux_id),
		.exc_cause_o(exc_cause),
		.illegal_c_insn_i(illegal_c_insn_id),
		.is_compressed_i(is_compressed_id),
		.pc_id_i(pc_id),
		.halt_if_o(halt_if),
		.id_ready_o(id_ready),
		.ex_ready_i(ex_ready),
		.id_valid_o(id_valid),
		.alu_operator_ex_o(alu_operator_ex),
		.alu_operand_a_ex_o(alu_operand_a_ex),
		.alu_operand_b_ex_o(alu_operand_b_ex),
		.ppu_operator_ex_o(ppu_operator_ex),
		.ppu_operand_a_ex_o(ppu_operand_a_ex),
		.ppu_operand_b_ex_o(ppu_operand_b_ex),
		.ppu_operand_c_ex_o(ppu_operand_c_ex),
		.ppu_en_ex_o(ppu_en_ex),
		.mult_en_ex_o(mult_en_ex),
		.div_en_ex_o(div_en_ex),
		.multdiv_operator_ex_o(multdiv_operator_ex),
		.multdiv_signed_mode_ex_o(multdiv_signed_mode_ex),
		.multdiv_operand_a_ex_o(multdiv_operand_a_ex),
		.multdiv_operand_b_ex_o(multdiv_operand_b_ex),
		.csr_access_ex_o(csr_access_ex),
		.csr_op_ex_o(csr_op_ex),
		.csr_cause_o(csr_cause),
		.csr_save_if_o(csr_save_if),
		.csr_save_id_o(csr_save_id),
		.csr_restore_mret_id_o(csr_restore_mret_id),
		.csr_save_cause_o(csr_save_cause),
		.data_req_ex_o(data_req_ex),
		.data_we_ex_o(data_we_ex),
		.data_type_ex_o(data_type_ex),
		.data_sign_ext_ex_o(data_sign_ext_ex),
		.data_reg_offset_ex_o(data_reg_offset_ex),
		.data_load_event_ex_o(data_load_event_ex),
		.data_wdata_ex_o(data_wdata_ex),
		.data_misaligned_i(data_misaligned),
		.misaligned_addr_i(misaligned_addr),
		.irq_i(irq_i),
		.irq_id_i(irq_id_i),
		.m_irq_enable_i(m_irq_enable),
		.irq_ack_o(irq_ack_o),
		.irq_id_o(irq_id_o),
		.lsu_load_err_i(lsu_load_err),
		.lsu_store_err_i(lsu_store_err),
		.dbg_settings_i(dbg_settings),
		.dbg_req_i(dbg_req),
		.dbg_ack_o(dbg_ack),
		.dbg_stall_i(dbg_stall),
		.dbg_trap_o(dbg_trap),
		.dbg_reg_rreq_i(dbg_reg_rreq),
		.dbg_reg_raddr_i(dbg_reg_raddr),
		.dbg_reg_rdata_o(dbg_reg_rdata),
		.dbg_reg_wreq_i(dbg_reg_wreq),
		.dbg_reg_waddr_i(dbg_reg_waddr),
		.dbg_reg_wdata_i(dbg_reg_wdata),
		.dbg_jump_req_i(dbg_jump_req),
		.regfile_wdata_lsu_i(regfile_wdata_lsu),
		.regfile_wdata_ex_i(regfile_wdata_ex),
		.csr_rdata_i(csr_rdata),
		.perf_jump_o(perf_jump),
		.perf_branch_o(perf_branch),
		.perf_tbranch_o(perf_tbranch)
	);
	zeroriscy_ex_block #(.RV32M(RV32M)) ex_block_i(
		.clk(clk),
		.rst_n(rst_ni),
		.alu_operator_i(alu_operator_ex),
		.multdiv_operator_i(multdiv_operator_ex),
		.alu_operand_a_i(alu_operand_a_ex),
		.alu_operand_b_i(alu_operand_b_ex),
		.ppu_en_i(ppu_en_ex),
		.ppu_operator_i(ppu_operator_ex),
		.ppu_operand_a_i(ppu_operand_a_ex),
		.ppu_operand_b_i(ppu_operand_b_ex),
		.ppu_operand_c_i(ppu_operand_c_ex),
		.ppu_result_o(ppu_result_ex),
		.mult_en_i(mult_en_ex),
		.div_en_i(div_en_ex),
		.multdiv_signed_mode_i(multdiv_signed_mode_ex),
		.multdiv_operand_a_i(multdiv_operand_a_ex),
		.multdiv_operand_b_i(multdiv_operand_b_ex),
		.alu_adder_result_ex_o(alu_adder_result_ex),
		.regfile_wdata_ex_o(regfile_wdata_ex),
		.jump_target_o(jump_target_ex),
		.branch_decision_o(branch_decision),
		.lsu_en_i(data_req_ex),
		.lsu_ready_ex_i(data_valid_lsu),
		.ex_ready_o(ex_ready)
	);
	zeroriscy_load_store_unit load_store_unit_i(
		.clk(clk),
		.rst_n(rst_ni),
		.data_req_o(data_req_o),
		.data_gnt_i(data_gnt_i),
		.data_rvalid_i(data_rvalid_i),
		.data_err_i(data_err_i),
		.data_addr_o(data_addr_o),
		.data_we_o(data_we_o),
		.data_be_o(data_be_o),
		.data_wdata_o(data_wdata_o),
		.data_rdata_i(data_rdata_i),
		.data_we_ex_i(data_we_ex),
		.data_type_ex_i(data_type_ex),
		.data_wdata_ex_i(data_wdata_ex),
		.data_reg_offset_ex_i(data_reg_offset_ex),
		.data_sign_ext_ex_i(data_sign_ext_ex),
		.data_rdata_ex_o(regfile_wdata_lsu),
		.data_req_ex_i(data_req_ex),
		.adder_result_ex_i(alu_adder_result_ex),
		.ppu_result_ex_i(ppu_result_ex),
		.data_misaligned_o(data_misaligned),
		.misaligned_addr_o(misaligned_addr),
		.load_err_o(lsu_load_err),
		.store_err_o(lsu_store_err),
		.data_valid_o(data_valid_lsu),
		.lsu_update_addr_o(),
		.busy_o(lsu_busy)
	);
	zeroriscy_cs_registers #(.N_EXT_CNT(N_EXT_PERF_COUNTERS)) cs_registers_i(
		.clk(clk),
		.rst_n(rst_ni),
		.core_id_i(core_id_i),
		.cluster_id_i(cluster_id_i),
		.boot_addr_i(boot_addr_i[31:8]),
		.csr_access_i(csr_access),
		.csr_addr_i(csr_addr),
		.csr_wdata_i(csr_wdata),
		.csr_op_i(csr_op),
		.csr_rdata_o(csr_rdata),
		.m_irq_enable_o(m_irq_enable),
		.mepc_o(mepc),
		.pc_if_i(pc_if),
		.pc_id_i(pc_id),
		.csr_save_if_i(csr_save_if),
		.csr_save_id_i(csr_save_id),
		.csr_restore_mret_i(csr_restore_mret_id),
		.csr_cause_i(csr_cause),
		.csr_save_cause_i(csr_save_cause),
		.if_valid_i(if_valid),
		.id_valid_i(id_valid),
		.is_compressed_i(is_compressed_id),
		.is_decoding_i(is_decoding),
		.imiss_i(perf_imiss),
		.pc_set_i(pc_set),
		.jump_i(perf_jump),
		.branch_i(perf_branch),
		.branch_taken_i(perf_tbranch),
		.mem_load_i((data_req_o & data_gnt_i) & ~data_we_o),
		.mem_store_i((data_req_o & data_gnt_i) & data_we_o),
		.ext_counters_i(ext_perf_counters_i)
	);
	assign csr_access = (dbg_csr_req == 1'b0 ? csr_access_ex : 1'b1);
	assign csr_addr = (dbg_csr_req == 1'b0 ? csr_addr_int : dbg_csr_addr);
	assign csr_wdata = (dbg_csr_req == 1'b0 ? alu_operand_a_ex : dbg_csr_wdata);
	localparam zeroriscy_defines_CSR_OP_NONE = 2'b00;
	localparam zeroriscy_defines_CSR_OP_WRITE = 2'b01;
	assign csr_op = (dbg_csr_req == 1'b0 ? csr_op_ex : (dbg_csr_we == 1'b1 ? zeroriscy_defines_CSR_OP_WRITE : zeroriscy_defines_CSR_OP_NONE));
	assign csr_addr_int = (csr_access_ex ? alu_operand_b_ex[11:0] : {12 {1'sb0}});
	zeroriscy_debug_unit debug_unit_i(
		.clk(clk_i),
		.rst_n(rst_ni),
		.debug_req_i(debug_req_i),
		.debug_gnt_o(debug_gnt_o),
		.debug_rvalid_o(debug_rvalid_o),
		.debug_addr_i(debug_addr_i),
		.debug_we_i(debug_we_i),
		.debug_wdata_i(debug_wdata_i),
		.debug_rdata_o(debug_rdata_o),
		.debug_halt_i(debug_halt_i),
		.debug_resume_i(debug_resume_i),
		.debug_halted_o(debug_halted_o),
		.settings_o(dbg_settings),
		.trap_i(dbg_trap),
		.exc_cause_i(exc_cause),
		.stall_o(dbg_stall),
		.dbg_req_o(dbg_req),
		.dbg_ack_i(dbg_ack),
		.regfile_rreq_o(dbg_reg_rreq),
		.regfile_raddr_o(dbg_reg_raddr),
		.regfile_rdata_i(dbg_reg_rdata),
		.regfile_wreq_o(dbg_reg_wreq),
		.regfile_waddr_o(dbg_reg_waddr),
		.regfile_wdata_o(dbg_reg_wdata),
		.csr_req_o(dbg_csr_req),
		.csr_addr_o(dbg_csr_addr),
		.csr_we_o(dbg_csr_we),
		.csr_wdata_o(dbg_csr_wdata),
		.csr_rdata_i(csr_rdata),
		.pc_if_i(pc_if),
		.pc_id_i(pc_id),
		.instr_valid_id_i(instr_valid_id),
		.sleeping_i(sleeping),
		.jump_addr_o(dbg_jump_addr),
		.jump_req_o(dbg_jump_req)
	);
	zeroriscy_tracer zeroriscy_tracer_i(
		.clk(clk_i),
		.rst_n(rst_ni),
		.fetch_enable(fetch_enable_i),
		.core_id(core_id_i),
		.cluster_id(cluster_id_i),
		.pc(id_stage_i.pc_id_i),
		.instr(id_stage_i.instr),
		.compressed(id_stage_i.is_compressed_i),
		.id_valid(id_stage_i.id_valid_o),
		.is_decoding(id_stage_i.is_decoding_o),
		.is_branch(id_stage_i.branch_in_id),
		.branch_taken(id_stage_i.branch_set_q),
		.pipe_flush(id_stage_i.controller_i.pipe_flush_i),
		.mret_insn(id_stage_i.controller_i.mret_insn_i),
		.ecall_insn(id_stage_i.controller_i.ecall_insn_i),
		.ebrk_insn(id_stage_i.controller_i.ebrk_insn_i),
		.csr_status(id_stage_i.controller_i.csr_status_i),
		.rs1_value(id_stage_i.operand_a_fw_id),
		.rs2_value(id_stage_i.operand_b_fw_id),
		.rs3_value(id_stage_i.operand_c_fw_id),
		.lsu_value(data_wdata_ex),
		.ex_reg_addr(id_stage_i.regfile_waddr_mux),
		.ex_reg_we(id_stage_i.regfile_we_mux),
		.ex_reg_wdata(id_stage_i.regfile_wdata_mux),
		.data_valid_lsu(data_valid_lsu),
		.ex_data_addr(data_addr_o),
		.ex_data_req(data_req_o),
		.ex_data_gnt(data_gnt_i),
		.ex_data_we(data_we_o),
		.ex_data_wdata(data_wdata_o),
		.lsu_reg_wdata(regfile_wdata_lsu),
		.imm_u_type(id_stage_i.imm_u_type),
		.imm_uj_type(id_stage_i.imm_uj_type),
		.imm_i_type(id_stage_i.imm_i_type),
		.imm_iz_type(id_stage_i.imm_iz_type[11:0]),
		.imm_z_type(id_stage_i.imm_z_type),
		.imm_s_type(id_stage_i.imm_s_type),
		.imm_sb_type(id_stage_i.imm_sb_type)
	);
endmodule
module zeroriscy_cs_registers (
	clk,
	rst_n,
	core_id_i,
	cluster_id_i,
	boot_addr_i,
	csr_access_i,
	csr_addr_i,
	csr_wdata_i,
	csr_op_i,
	csr_rdata_o,
	m_irq_enable_o,
	mepc_o,
	pc_if_i,
	pc_id_i,
	csr_save_if_i,
	csr_save_id_i,
	csr_restore_mret_i,
	csr_cause_i,
	csr_save_cause_i,
	if_valid_i,
	id_valid_i,
	is_compressed_i,
	is_decoding_i,
	imiss_i,
	pc_set_i,
	jump_i,
	branch_i,
	branch_taken_i,
	mem_load_i,
	mem_store_i,
	ext_counters_i
);
	reg _sv2v_0;
	parameter N_EXT_CNT = 0;
	input wire clk;
	input wire rst_n;
	input wire [3:0] core_id_i;
	input wire [5:0] cluster_id_i;
	input wire [23:0] boot_addr_i;
	input wire csr_access_i;
	input wire [11:0] csr_addr_i;
	input wire [31:0] csr_wdata_i;
	input wire [1:0] csr_op_i;
	output reg [31:0] csr_rdata_o;
	output wire m_irq_enable_o;
	output wire [31:0] mepc_o;
	input wire [31:0] pc_if_i;
	input wire [31:0] pc_id_i;
	input wire csr_save_if_i;
	input wire csr_save_id_i;
	input wire csr_restore_mret_i;
	input wire [5:0] csr_cause_i;
	input wire csr_save_cause_i;
	input wire if_valid_i;
	input wire id_valid_i;
	input wire is_compressed_i;
	input wire is_decoding_i;
	input wire imiss_i;
	input wire pc_set_i;
	input wire jump_i;
	input wire branch_i;
	input wire branch_taken_i;
	input wire mem_load_i;
	input wire mem_store_i;
	input wire [N_EXT_CNT - 1:0] ext_counters_i;
	localparam N_PERF_COUNTERS = 11 + N_EXT_CNT;
	localparam N_PERF_REGS = N_PERF_COUNTERS;
	reg id_valid_q;
	wire [N_PERF_COUNTERS - 1:0] PCCR_in;
	reg [N_PERF_COUNTERS - 1:0] PCCR_inc;
	reg [N_PERF_COUNTERS - 1:0] PCCR_inc_q;
	reg [(N_PERF_REGS * 32) - 1:0] PCCR_q;
	reg [(N_PERF_REGS * 32) - 1:0] PCCR_n;
	reg [1:0] PCMR_n;
	reg [1:0] PCMR_q;
	reg [N_PERF_COUNTERS - 1:0] PCER_n;
	reg [N_PERF_COUNTERS - 1:0] PCER_q;
	reg [31:0] perf_rdata;
	reg [4:0] pccr_index;
	reg pccr_all_sel;
	reg is_pccr;
	reg is_pcer;
	reg is_pcmr;
	reg [31:0] csr_wdata_int;
	reg [31:0] csr_rdata_int;
	reg csr_we_int;
	reg [31:0] mepc_q;
	reg [31:0] mepc_n;
	reg [5:0] mcause_q;
	reg [5:0] mcause_n;
	reg [3:0] mstatus_q;
	reg [3:0] mstatus_n;
	always @(*) begin
		if (_sv2v_0)
			;
		csr_rdata_int = 1'sb0;
		case (csr_addr_i)
			12'h300: csr_rdata_int = {19'b0000000000000000000, mstatus_q[1-:2], 3'b000, mstatus_q[2], 3'h0, mstatus_q[3], 3'h0};
			12'h305: csr_rdata_int = {boot_addr_i, 8'h00};
			12'h341: csr_rdata_int = mepc_q;
			12'h342: csr_rdata_int = {mcause_q[5], 26'b00000000000000000000000000, mcause_q[4:0]};
			12'hf14: csr_rdata_int = {21'b000000000000000000000, cluster_id_i[5:0], 1'b0, core_id_i[3:0]};
			default:
				;
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		mepc_n = mepc_q;
		mstatus_n = mstatus_q;
		mcause_n = mcause_q;
		case (csr_addr_i)
			12'h300:
				if (csr_we_int)
					mstatus_n = {csr_wdata_int[3], csr_wdata_int[7], 2'b11};
			12'h341:
				if (csr_we_int)
					mepc_n = csr_wdata_int;
			12'h342:
				if (csr_we_int)
					mcause_n = {csr_wdata_int[31], csr_wdata_int[4:0]};
			default:
				;
		endcase
		(* full_case, parallel_case *)
		case (1'b1)
			csr_save_cause_i: begin
				(* full_case, parallel_case *)
				case (1'b1)
					csr_save_if_i: mepc_n = pc_if_i;
					csr_save_id_i: mepc_n = pc_id_i;
					default:
						;
				endcase
				mstatus_n[2] = mstatus_q[3];
				mstatus_n[3] = 1'b0;
				mcause_n = csr_cause_i;
			end
			csr_restore_mret_i: begin
				mstatus_n[3] = mstatus_q[2];
				mstatus_n[2] = 1'b1;
			end
			default:
				;
		endcase
	end
	localparam zeroriscy_defines_CSR_OP_CLEAR = 2'b11;
	localparam zeroriscy_defines_CSR_OP_NONE = 2'b00;
	localparam zeroriscy_defines_CSR_OP_SET = 2'b10;
	localparam zeroriscy_defines_CSR_OP_WRITE = 2'b01;
	always @(*) begin
		if (_sv2v_0)
			;
		csr_wdata_int = csr_wdata_i;
		csr_we_int = 1'b1;
		(* full_case, parallel_case *)
		case (csr_op_i)
			zeroriscy_defines_CSR_OP_WRITE: csr_wdata_int = csr_wdata_i;
			zeroriscy_defines_CSR_OP_SET: csr_wdata_int = csr_wdata_i | csr_rdata_o;
			zeroriscy_defines_CSR_OP_CLEAR: csr_wdata_int = ~csr_wdata_i & csr_rdata_o;
			zeroriscy_defines_CSR_OP_NONE: begin
				csr_wdata_int = csr_wdata_i;
				csr_we_int = 1'b0;
			end
			default:
				;
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		csr_rdata_o = csr_rdata_int;
		if ((is_pccr || is_pcer) || is_pcmr)
			csr_rdata_o = perf_rdata;
	end
	assign m_irq_enable_o = mstatus_q[3];
	assign mepc_o = mepc_q;
	always @(posedge clk or negedge rst_n)
		if (rst_n == 1'b0) begin
			mstatus_q <= 4'b0011;
			mepc_q <= 1'sb0;
			mcause_q <= 1'sb0;
		end
		else begin
			mstatus_q <= {mstatus_n[3], mstatus_n[2], 2'b11};
			mepc_q <= mepc_n;
			mcause_q <= mcause_n;
		end
	assign PCCR_in[0] = 1'b1;
	assign PCCR_in[1] = if_valid_i;
	assign PCCR_in[2] = 1'b0;
	assign PCCR_in[3] = 1'b0;
	assign PCCR_in[4] = imiss_i & ~pc_set_i;
	assign PCCR_in[5] = mem_load_i;
	assign PCCR_in[6] = mem_store_i;
	assign PCCR_in[7] = jump_i;
	assign PCCR_in[8] = branch_i;
	assign PCCR_in[9] = branch_taken_i;
	assign PCCR_in[10] = (id_valid_i & is_decoding_i) & is_compressed_i;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < N_EXT_CNT; _gv_i_1 = _gv_i_1 + 1) begin : g_extcounters
			localparam i = _gv_i_1;
			assign PCCR_in[(N_PERF_COUNTERS - N_EXT_CNT) + i] = ext_counters_i[i];
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		is_pccr = 1'b0;
		is_pcmr = 1'b0;
		is_pcer = 1'b0;
		pccr_all_sel = 1'b0;
		pccr_index = 1'sb0;
		perf_rdata = 1'sb0;
		if (csr_access_i) begin
			(* full_case, parallel_case *)
			case (csr_addr_i)
				12'h7a0: begin
					is_pcer = 1'b1;
					perf_rdata[15:0] = PCER_q;
				end
				12'h7a1: begin
					is_pcmr = 1'b1;
					perf_rdata[1:0] = PCMR_q;
				end
				12'h79f: begin
					is_pccr = 1'b1;
					pccr_all_sel = 1'b1;
				end
				default:
					;
			endcase
			if (csr_addr_i[11:5] == 7'b0111100) begin
				is_pccr = 1'b1;
				pccr_index = csr_addr_i[4:0];
				perf_rdata = PCCR_q[csr_addr_i[4:0] * 32+:32];
			end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N_PERF_COUNTERS; i = i + 1)
				begin : PERF_CNT_INC
					PCCR_inc[i] = (PCCR_in[i] & PCER_q[i]) & PCMR_q[0];
					PCCR_n[i * 32+:32] = PCCR_q[i * 32+:32];
					if ((PCCR_inc_q[i] == 1'b1) && ((PCCR_q[i * 32+:32] != 32'hffffffff) || (PCMR_q[1] == 1'b0)))
						PCCR_n[i * 32+:32] = PCCR_q[i * 32+:32] + 1;
					if ((is_pccr == 1'b1) && ((pccr_all_sel == 1'b1) || (pccr_index == i)))
						(* full_case, parallel_case *)
						case (csr_op_i)
							zeroriscy_defines_CSR_OP_NONE:
								;
							zeroriscy_defines_CSR_OP_WRITE: PCCR_n[i * 32+:32] = csr_wdata_i;
							zeroriscy_defines_CSR_OP_SET: PCCR_n[i * 32+:32] = csr_wdata_i | PCCR_q[i * 32+:32];
							zeroriscy_defines_CSR_OP_CLEAR: PCCR_n[i * 32+:32] = csr_wdata_i & ~PCCR_q[i * 32+:32];
						endcase
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		PCMR_n = PCMR_q;
		PCER_n = PCER_q;
		if (is_pcmr)
			(* full_case, parallel_case *)
			case (csr_op_i)
				zeroriscy_defines_CSR_OP_NONE:
					;
				zeroriscy_defines_CSR_OP_WRITE: PCMR_n = csr_wdata_i[1:0];
				zeroriscy_defines_CSR_OP_SET: PCMR_n = csr_wdata_i[1:0] | PCMR_q;
				zeroriscy_defines_CSR_OP_CLEAR: PCMR_n = csr_wdata_i[1:0] & ~PCMR_q;
			endcase
		if (is_pcer)
			(* full_case, parallel_case *)
			case (csr_op_i)
				zeroriscy_defines_CSR_OP_NONE:
					;
				zeroriscy_defines_CSR_OP_WRITE: PCER_n = csr_wdata_i[N_PERF_COUNTERS - 1:0];
				zeroriscy_defines_CSR_OP_SET: PCER_n = csr_wdata_i[N_PERF_COUNTERS - 1:0] | PCER_q;
				zeroriscy_defines_CSR_OP_CLEAR: PCER_n = csr_wdata_i[N_PERF_COUNTERS - 1:0] & ~PCER_q;
			endcase
	end
	always @(posedge clk or negedge rst_n)
		if (rst_n == 1'b0) begin
			id_valid_q <= 1'b0;
			PCER_q <= 1'sb0;
			PCMR_q <= 2'h3;
			begin : sv2v_autoblock_2
				reg signed [31:0] i;
				for (i = 0; i < N_PERF_REGS; i = i + 1)
					begin
						PCCR_q[i * 32+:32] <= 1'sb0;
						PCCR_inc_q[i] <= 1'sb0;
					end
			end
		end
		else begin
			id_valid_q <= id_valid_i;
			PCER_q <= PCER_n;
			PCMR_q <= PCMR_n;
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < N_PERF_REGS; i = i + 1)
					begin
						PCCR_q[i * 32+:32] <= PCCR_n[i * 32+:32];
						PCCR_inc_q[i] <= PCCR_inc[i];
					end
			end
		end
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_debug_unit (
	clk,
	rst_n,
	debug_req_i,
	debug_gnt_o,
	debug_rvalid_o,
	debug_addr_i,
	debug_we_i,
	debug_wdata_i,
	debug_rdata_o,
	debug_halted_o,
	debug_halt_i,
	debug_resume_i,
	settings_o,
	trap_i,
	exc_cause_i,
	stall_o,
	dbg_req_o,
	dbg_ack_i,
	regfile_rreq_o,
	regfile_raddr_o,
	regfile_rdata_i,
	regfile_wreq_o,
	regfile_waddr_o,
	regfile_wdata_o,
	csr_req_o,
	csr_addr_o,
	csr_we_o,
	csr_wdata_o,
	csr_rdata_i,
	pc_if_i,
	pc_id_i,
	instr_valid_id_i,
	sleeping_i,
	jump_req_o,
	jump_addr_o
);
	reg _sv2v_0;
	parameter REG_ADDR_WIDTH = 5;
	input wire clk;
	input wire rst_n;
	input wire debug_req_i;
	output reg debug_gnt_o;
	output reg debug_rvalid_o;
	input wire [14:0] debug_addr_i;
	input wire debug_we_i;
	input wire [31:0] debug_wdata_i;
	output reg [31:0] debug_rdata_o;
	output reg debug_halted_o;
	input wire debug_halt_i;
	input wire debug_resume_i;
	localparam zeroriscy_defines_DBG_SETS_W = 6;
	output wire [5:0] settings_o;
	input wire trap_i;
	input wire [5:0] exc_cause_i;
	output reg stall_o;
	output reg dbg_req_o;
	input wire dbg_ack_i;
	output wire regfile_rreq_o;
	output wire [REG_ADDR_WIDTH - 1:0] regfile_raddr_o;
	input wire [31:0] regfile_rdata_i;
	output wire regfile_wreq_o;
	output wire [REG_ADDR_WIDTH - 1:0] regfile_waddr_o;
	output wire [31:0] regfile_wdata_o;
	output wire csr_req_o;
	output wire [11:0] csr_addr_o;
	output reg csr_we_o;
	output wire [31:0] csr_wdata_o;
	input wire [31:0] csr_rdata_i;
	input wire [31:0] pc_if_i;
	input wire [31:0] pc_id_i;
	input wire instr_valid_id_i;
	input wire sleeping_i;
	output wire jump_req_o;
	output wire [31:0] jump_addr_o;
	reg [2:0] rdata_sel_q;
	reg [2:0] rdata_sel_n;
	reg [0:0] state_q;
	reg [0:0] state_n;
	reg [5:0] settings_q;
	reg [5:0] settings_n;
	reg [14:0] addr_q;
	reg [31:0] wdata_q;
	reg regfile_rreq_q;
	reg regfile_rreq_n;
	reg jump_req_q;
	reg jump_req_n;
	reg csr_req_q;
	reg csr_req_n;
	reg regfile_wreq;
	reg [1:0] stall_cs;
	reg [1:0] stall_ns;
	reg [31:0] dbg_rdata;
	reg dbg_resume;
	reg dbg_halt;
	reg [5:0] dbg_cause_q;
	reg [5:0] dbg_cause_n;
	reg dbg_ssth_q;
	reg dbg_ssth_n;
	reg ssth_clear;
	wire [31:0] ppc_int;
	wire [31:0] npc_int;
	localparam zeroriscy_defines_DBG_SETS_EBRK = 1;
	localparam zeroriscy_defines_DBG_SETS_ECALL = 4;
	localparam zeroriscy_defines_DBG_SETS_EILL = 3;
	localparam zeroriscy_defines_DBG_SETS_ELSU = 2;
	localparam zeroriscy_defines_DBG_SETS_SSTE = 0;
	always @(*) begin
		if (_sv2v_0)
			;
		rdata_sel_n = 3'd0;
		state_n = 1'd0;
		debug_gnt_o = 1'b0;
		regfile_rreq_n = 1'b0;
		regfile_wreq = 1'b0;
		csr_req_n = 1'b0;
		csr_we_o = 1'b0;
		jump_req_n = 1'b0;
		dbg_resume = 1'b0;
		dbg_halt = 1'b0;
		settings_n = settings_q;
		ssth_clear = 1'b0;
		if (debug_req_i) begin
			if (debug_we_i) begin
				if (debug_addr_i[14]) begin
					if (state_q == 1'd0) begin
						debug_gnt_o = 1'b0;
						state_n = 1'd1;
						if (debug_halted_o)
							csr_req_n = 1'b1;
					end
					else begin
						debug_gnt_o = 1'b1;
						state_n = 1'd0;
						csr_we_o = 1'b1;
					end
				end
				else
					(* full_case, parallel_case *)
					case (debug_addr_i[13:8])
						6'b000000: begin
							debug_gnt_o = 1'b1;
							(* full_case, parallel_case *)
							case (debug_addr_i[6:2])
								5'b00000: begin
									if (debug_wdata_i[16]) begin
										if (~debug_halted_o)
											dbg_halt = 1'b1;
									end
									else if (debug_halted_o)
										dbg_resume = 1'b1;
									settings_n[zeroriscy_defines_DBG_SETS_SSTE] = debug_wdata_i[0];
								end
								5'b00001: ssth_clear = debug_wdata_i[0];
								5'b00010: begin
									settings_n[zeroriscy_defines_DBG_SETS_ECALL] = debug_wdata_i[11];
									settings_n[zeroriscy_defines_DBG_SETS_ELSU] = debug_wdata_i[7] | debug_wdata_i[5];
									settings_n[zeroriscy_defines_DBG_SETS_EBRK] = debug_wdata_i[3];
									settings_n[zeroriscy_defines_DBG_SETS_EILL] = debug_wdata_i[2];
								end
								default:
									;
							endcase
						end
						6'b100000: begin
							debug_gnt_o = 1'b1;
							if (debug_halted_o)
								(* full_case, parallel_case *)
								case (debug_addr_i[6:2])
									5'b00000: jump_req_n = 1'b1;
									default:
										;
								endcase
						end
						6'b000100: begin
							debug_gnt_o = 1'b1;
							if (debug_halted_o)
								regfile_wreq = 1'b1;
						end
						default: debug_gnt_o = 1'b1;
					endcase
			end
			else if (debug_addr_i[14]) begin
				debug_gnt_o = 1'b1;
				if (debug_halted_o) begin
					csr_req_n = 1'b1;
					rdata_sel_n = 3'd1;
				end
			end
			else
				(* full_case, parallel_case *)
				case (debug_addr_i[13:8])
					6'b000000: begin
						debug_gnt_o = 1'b1;
						rdata_sel_n = 3'd3;
					end
					6'b100000: begin
						debug_gnt_o = 1'b1;
						rdata_sel_n = 3'd4;
					end
					6'b000100: begin
						debug_gnt_o = 1'b1;
						if (debug_halted_o) begin
							regfile_rreq_n = 1'b1;
							rdata_sel_n = 3'd2;
						end
					end
					default: debug_gnt_o = 1'b1;
				endcase
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		dbg_rdata = 1'sb0;
		case (rdata_sel_q)
			3'd3:
				(* full_case, parallel_case *)
				case (addr_q[6:2])
					5'h00: dbg_rdata[31:0] = {15'b000000000000000, debug_halted_o, 15'b000000000000000, settings_q[zeroriscy_defines_DBG_SETS_SSTE]};
					5'h01: dbg_rdata[31:0] = {15'b000000000000000, sleeping_i, 15'b000000000000000, dbg_ssth_q};
					5'h02: begin
						dbg_rdata[31:16] = 1'sb0;
						dbg_rdata[15:12] = 1'sb0;
						dbg_rdata[11] = settings_q[zeroriscy_defines_DBG_SETS_ECALL];
						dbg_rdata[10:8] = 1'sb0;
						dbg_rdata[7] = settings_q[zeroriscy_defines_DBG_SETS_ELSU];
						dbg_rdata[6] = 1'b0;
						dbg_rdata[5] = settings_q[zeroriscy_defines_DBG_SETS_ELSU];
						dbg_rdata[4] = 1'b0;
						dbg_rdata[3] = settings_q[zeroriscy_defines_DBG_SETS_EBRK];
						dbg_rdata[2] = settings_q[zeroriscy_defines_DBG_SETS_EILL];
						dbg_rdata[1:0] = 1'sb0;
					end
					5'h03: dbg_rdata = {dbg_cause_q[5], 26'b00000000000000000000000000, dbg_cause_q[4:0]};
					5'h10: dbg_rdata = 1'sb0;
					5'h12: dbg_rdata = 1'sb0;
					5'h14: dbg_rdata = 1'sb0;
					5'h16: dbg_rdata = 1'sb0;
					5'h18: dbg_rdata = 1'sb0;
					5'h1a: dbg_rdata = 1'sb0;
					5'h1c: dbg_rdata = 1'sb0;
					5'h1e: dbg_rdata = 1'sb0;
					default:
						;
				endcase
			3'd4:
				(* full_case, parallel_case *)
				case (addr_q[2:2])
					1'b0: dbg_rdata = npc_int;
					1'b1: dbg_rdata = ppc_int;
					default:
						;
				endcase
			default:
				;
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		debug_rdata_o = 1'sb0;
		case (rdata_sel_q)
			3'd1: debug_rdata_o = csr_rdata_i;
			3'd2: debug_rdata_o = regfile_rdata_i;
			3'd3: debug_rdata_o = dbg_rdata;
			3'd4: debug_rdata_o = dbg_rdata;
			default:
				;
		endcase
	end
	always @(posedge clk or negedge rst_n)
		if (~rst_n)
			debug_rvalid_o <= 1'b0;
		else
			debug_rvalid_o <= debug_gnt_o;
	localparam zeroriscy_defines_DBG_CAUSE_HALT = 6'h1f;
	always @(*) begin
		if (_sv2v_0)
			;
		stall_ns = stall_cs;
		dbg_req_o = 1'b0;
		stall_o = 1'b0;
		debug_halted_o = 1'b0;
		dbg_cause_n = dbg_cause_q;
		dbg_ssth_n = dbg_ssth_q;
		case (stall_cs)
			2'd0: begin
				dbg_ssth_n = 1'b0;
				if ((dbg_halt | debug_halt_i) | trap_i) begin
					dbg_req_o = 1'b1;
					stall_ns = 2'd1;
					if (trap_i) begin
						if (settings_q[zeroriscy_defines_DBG_SETS_SSTE])
							dbg_ssth_n = 1'b1;
						dbg_cause_n = exc_cause_i;
					end
					else
						dbg_cause_n = zeroriscy_defines_DBG_CAUSE_HALT;
				end
			end
			2'd1: begin
				dbg_req_o = 1'b1;
				if (dbg_ack_i)
					stall_ns = 2'd2;
				if (dbg_resume | debug_resume_i)
					stall_ns = 2'd0;
			end
			2'd2: begin
				stall_o = 1'b1;
				debug_halted_o = 1'b1;
				if (dbg_resume | debug_resume_i) begin
					stall_ns = 2'd0;
					stall_o = 1'b0;
				end
			end
		endcase
		if (ssth_clear)
			dbg_ssth_n = 1'b0;
	end
	always @(posedge clk or negedge rst_n)
		if (~rst_n) begin
			stall_cs <= 2'd0;
			dbg_cause_q <= zeroriscy_defines_DBG_CAUSE_HALT;
			dbg_ssth_q <= 1'b0;
		end
		else begin
			stall_cs <= stall_ns;
			dbg_cause_q <= dbg_cause_n;
			dbg_ssth_q <= dbg_ssth_n;
		end
	assign ppc_int = pc_id_i;
	assign npc_int = pc_if_i;
	always @(posedge clk or negedge rst_n)
		if (~rst_n) begin
			addr_q <= 1'sb0;
			wdata_q <= 1'sb0;
			state_q <= 1'd0;
			rdata_sel_q <= 3'd0;
			regfile_rreq_q <= 1'b0;
			csr_req_q <= 1'b0;
			jump_req_q <= 1'b0;
			settings_q <= 1'b0;
		end
		else begin
			settings_q <= settings_n;
			if (debug_req_i) begin
				addr_q <= debug_addr_i;
				wdata_q <= debug_wdata_i;
				state_q <= state_n;
			end
			if (debug_req_i | debug_rvalid_o) begin
				regfile_rreq_q <= regfile_rreq_n;
				csr_req_q <= csr_req_n;
				jump_req_q <= jump_req_n;
				rdata_sel_q <= rdata_sel_n;
			end
		end
	assign regfile_rreq_o = regfile_rreq_q;
	assign regfile_raddr_o = addr_q[6:2];
	assign regfile_wreq_o = regfile_wreq;
	assign regfile_waddr_o = debug_addr_i[6:2];
	assign regfile_wdata_o = debug_wdata_i;
	assign csr_req_o = csr_req_q;
	assign csr_addr_o = addr_q[13:2];
	assign csr_wdata_o = wdata_q;
	assign jump_req_o = jump_req_q;
	assign jump_addr_o = wdata_q;
	assign settings_o = settings_q;
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_decoder (
	deassert_we_i,
	data_misaligned_i,
	branch_mux_i,
	jump_mux_i,
	illegal_insn_o,
	ebrk_insn_o,
	mret_insn_o,
	ecall_insn_o,
	pipe_flush_o,
	instr_rdata_i,
	illegal_c_insn_i,
	alu_operator_o,
	alu_op_a_mux_sel_o,
	alu_op_b_mux_sel_o,
	imm_a_mux_sel_o,
	imm_b_mux_sel_o,
	mult_int_en_o,
	div_int_en_o,
	multdiv_operator_o,
	multdiv_signed_mode_o,
	ppu_en_o,
	ppu_operator_o,
	ppu_op_a_mux_sel_o,
	ppu_op_b_mux_sel_o,
	ppu_op_c_mux_sel_o,
	regfile_we_o,
	csr_access_o,
	csr_op_o,
	csr_status_o,
	data_req_o,
	data_we_o,
	data_type_o,
	data_sign_extension_o,
	data_reg_offset_o,
	data_load_event_o,
	jump_in_id_o,
	branch_in_id_o
);
	reg _sv2v_0;
	parameter RV32M = 1;
	input wire deassert_we_i;
	input wire data_misaligned_i;
	input wire branch_mux_i;
	input wire jump_mux_i;
	output reg illegal_insn_o;
	output reg ebrk_insn_o;
	output reg mret_insn_o;
	output reg ecall_insn_o;
	output reg pipe_flush_o;
	input wire [31:0] instr_rdata_i;
	input wire illegal_c_insn_i;
	localparam zeroriscy_defines_ALU_OP_WIDTH = 6;
	output reg [5:0] alu_operator_o;
	output reg [2:0] alu_op_a_mux_sel_o;
	output reg [2:0] alu_op_b_mux_sel_o;
	output reg [0:0] imm_a_mux_sel_o;
	output reg [3:0] imm_b_mux_sel_o;
	output wire mult_int_en_o;
	output wire div_int_en_o;
	output reg [1:0] multdiv_operator_o;
	output reg [1:0] multdiv_signed_mode_o;
	output wire ppu_en_o;
	localparam zeroriscy_defines_PPU_OP_WIDTH = 3;
	output reg [2:0] ppu_operator_o;
	output reg [2:0] ppu_op_a_mux_sel_o;
	output reg [2:0] ppu_op_b_mux_sel_o;
	output reg [2:0] ppu_op_c_mux_sel_o;
	output wire regfile_we_o;
	output reg csr_access_o;
	output wire [1:0] csr_op_o;
	output reg csr_status_o;
	output wire data_req_o;
	output reg data_we_o;
	output reg [1:0] data_type_o;
	output reg data_sign_extension_o;
	output reg [1:0] data_reg_offset_o;
	output reg data_load_event_o;
	output wire jump_in_id_o;
	output wire branch_in_id_o;
	reg regfile_we;
	reg data_req;
	reg mult_int_en;
	reg div_int_en;
	reg ppu_en;
	reg branch_in_id;
	reg jump_in_id;
	reg [1:0] csr_op;
	reg csr_illegal;
	localparam zeroriscy_defines_ALU_ADD = 6'b011000;
	localparam zeroriscy_defines_ALU_AND = 6'b010101;
	localparam zeroriscy_defines_ALU_EQ = 6'b001100;
	localparam zeroriscy_defines_ALU_GES = 6'b001010;
	localparam zeroriscy_defines_ALU_GEU = 6'b001011;
	localparam zeroriscy_defines_ALU_LTS = 6'b000000;
	localparam zeroriscy_defines_ALU_LTU = 6'b000001;
	localparam zeroriscy_defines_ALU_NE = 6'b001101;
	localparam zeroriscy_defines_ALU_OR = 6'b101110;
	localparam zeroriscy_defines_ALU_SLL = 6'b100111;
	localparam zeroriscy_defines_ALU_SLTS = 6'b000010;
	localparam zeroriscy_defines_ALU_SLTU = 6'b000011;
	localparam zeroriscy_defines_ALU_SRA = 6'b100100;
	localparam zeroriscy_defines_ALU_SRL = 6'b100101;
	localparam zeroriscy_defines_ALU_SUB = 6'b011001;
	localparam zeroriscy_defines_ALU_XOR = 6'b101111;
	localparam zeroriscy_defines_CSR_OP_CLEAR = 2'b11;
	localparam zeroriscy_defines_CSR_OP_NONE = 2'b00;
	localparam zeroriscy_defines_CSR_OP_SET = 2'b10;
	localparam zeroriscy_defines_CSR_OP_WRITE = 2'b01;
	localparam zeroriscy_defines_FLOAT_TO_POSIT = 3'd6;
	localparam zeroriscy_defines_FMADD_C = 3'd5;
	localparam zeroriscy_defines_FMADD_S = 3'd4;
	localparam zeroriscy_defines_IMMA_Z = 1'b0;
	localparam zeroriscy_defines_IMMA_ZERO = 1'b1;
	localparam zeroriscy_defines_IMMB_I = 4'b0000;
	localparam zeroriscy_defines_IMMB_PCINCR = 4'b0011;
	localparam zeroriscy_defines_IMMB_S = 4'b0001;
	localparam zeroriscy_defines_IMMB_SB = 4'b1101;
	localparam zeroriscy_defines_IMMB_U = 4'b0010;
	localparam zeroriscy_defines_IMMB_UJ = 4'b1100;
	localparam zeroriscy_defines_MD_OP_DIV = 2'b10;
	localparam zeroriscy_defines_MD_OP_MULH = 2'b01;
	localparam zeroriscy_defines_MD_OP_MULL = 2'b00;
	localparam zeroriscy_defines_MD_OP_REM = 2'b11;
	localparam zeroriscy_defines_OPCODE_AUIPC = 7'h17;
	localparam zeroriscy_defines_OPCODE_BRANCH = 7'h63;
	localparam zeroriscy_defines_OPCODE_JAL = 7'h6f;
	localparam zeroriscy_defines_OPCODE_JALR = 7'h67;
	localparam zeroriscy_defines_OPCODE_LOAD = 7'h03;
	localparam zeroriscy_defines_OPCODE_LUI = 7'h37;
	localparam zeroriscy_defines_OPCODE_OP = 7'h33;
	localparam zeroriscy_defines_OPCODE_OPIMM = 7'h13;
	localparam zeroriscy_defines_OPCODE_PPU_OP = 7'h0b;
	localparam zeroriscy_defines_OPCODE_PPU_OPIMM = 7'h2b;
	localparam zeroriscy_defines_OPCODE_STORE = 7'h23;
	localparam zeroriscy_defines_OPCODE_SYSTEM = 7'h73;
	localparam zeroriscy_defines_OP_A_CURRPC = 3'b001;
	localparam zeroriscy_defines_OP_A_IMM = 3'b010;
	localparam zeroriscy_defines_OP_A_REGA_OR_FWD = 3'b000;
	localparam zeroriscy_defines_OP_B_IMM = 3'b010;
	localparam zeroriscy_defines_OP_B_REGB_OR_FWD = 3'b000;
	localparam zeroriscy_defines_OP_C_REGC_OR_FWD = 3'b000;
	localparam zeroriscy_defines_POSIT_TO_FLOAT = 3'd7;
	localparam zeroriscy_defines_PPU_ADD = 3'd0;
	localparam zeroriscy_defines_PPU_DIV = 3'd3;
	localparam zeroriscy_defines_PPU_MUL = 3'd2;
	localparam zeroriscy_defines_PPU_SUB = 3'd1;
	always @(*) begin
		if (_sv2v_0)
			;
		jump_in_id = 1'b0;
		branch_in_id = 1'b0;
		alu_operator_o = zeroriscy_defines_ALU_SLTU;
		alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_REGA_OR_FWD;
		alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_REGB_OR_FWD;
		ppu_operator_o = zeroriscy_defines_PPU_ADD;
		ppu_op_a_mux_sel_o = zeroriscy_defines_OP_A_REGA_OR_FWD;
		ppu_op_b_mux_sel_o = zeroriscy_defines_OP_B_REGB_OR_FWD;
		ppu_op_c_mux_sel_o = zeroriscy_defines_OP_C_REGC_OR_FWD;
		imm_a_mux_sel_o = zeroriscy_defines_IMMA_ZERO;
		imm_b_mux_sel_o = zeroriscy_defines_IMMB_I;
		mult_int_en = 1'b0;
		div_int_en = 1'b0;
		ppu_en = 1'b0;
		multdiv_operator_o = zeroriscy_defines_MD_OP_MULL;
		multdiv_signed_mode_o = 2'b00;
		regfile_we = 1'b0;
		csr_access_o = 1'b0;
		csr_status_o = 1'b0;
		csr_illegal = 1'b0;
		csr_op = zeroriscy_defines_CSR_OP_NONE;
		data_we_o = 1'b0;
		data_type_o = 2'b00;
		data_sign_extension_o = 1'b0;
		data_reg_offset_o = 2'b00;
		data_req = 1'b0;
		data_load_event_o = 1'b0;
		illegal_insn_o = 1'b0;
		ebrk_insn_o = 1'b0;
		mret_insn_o = 1'b0;
		ecall_insn_o = 1'b0;
		pipe_flush_o = 1'b0;
		(* full_case, parallel_case *)
		case (instr_rdata_i[6:0])
			zeroriscy_defines_OPCODE_JAL: begin
				jump_in_id = 1'b1;
				if (jump_mux_i) begin
					alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_CURRPC;
					alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
					imm_b_mux_sel_o = zeroriscy_defines_IMMB_UJ;
					alu_operator_o = zeroriscy_defines_ALU_ADD;
					regfile_we = 1'b0;
				end
				else begin
					alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_CURRPC;
					alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
					imm_b_mux_sel_o = zeroriscy_defines_IMMB_PCINCR;
					alu_operator_o = zeroriscy_defines_ALU_ADD;
					regfile_we = 1'b1;
				end
			end
			zeroriscy_defines_OPCODE_JALR: begin
				jump_in_id = 1'b1;
				if (jump_mux_i) begin
					alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_REGA_OR_FWD;
					alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
					imm_b_mux_sel_o = zeroriscy_defines_IMMB_I;
					alu_operator_o = zeroriscy_defines_ALU_ADD;
					regfile_we = 1'b0;
				end
				else begin
					alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_CURRPC;
					alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
					imm_b_mux_sel_o = zeroriscy_defines_IMMB_PCINCR;
					alu_operator_o = zeroriscy_defines_ALU_ADD;
					regfile_we = 1'b1;
				end
				if (instr_rdata_i[14:12] != 3'b000) begin
					jump_in_id = 1'b0;
					regfile_we = 1'b0;
					illegal_insn_o = 1'b1;
				end
			end
			zeroriscy_defines_OPCODE_BRANCH: begin
				branch_in_id = 1'b1;
				if (branch_mux_i)
					(* full_case, parallel_case *)
					case (instr_rdata_i[14:12])
						3'b000: alu_operator_o = zeroriscy_defines_ALU_EQ;
						3'b001: alu_operator_o = zeroriscy_defines_ALU_NE;
						3'b100: alu_operator_o = zeroriscy_defines_ALU_LTS;
						3'b101: alu_operator_o = zeroriscy_defines_ALU_GES;
						3'b110: alu_operator_o = zeroriscy_defines_ALU_LTU;
						3'b111: alu_operator_o = zeroriscy_defines_ALU_GEU;
						default: illegal_insn_o = 1'b1;
					endcase
				else begin
					alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_CURRPC;
					alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
					imm_b_mux_sel_o = zeroriscy_defines_IMMB_SB;
					alu_operator_o = zeroriscy_defines_ALU_ADD;
					regfile_we = 1'b0;
				end
			end
			zeroriscy_defines_OPCODE_STORE: begin
				data_req = 1'b1;
				data_we_o = 1'b1;
				alu_operator_o = zeroriscy_defines_ALU_ADD;
				if (instr_rdata_i[14] == 1'b0) begin
					imm_b_mux_sel_o = zeroriscy_defines_IMMB_S;
					alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
				end
				else begin
					data_req = 1'b0;
					data_we_o = 1'b0;
					illegal_insn_o = 1'b1;
				end
				(* full_case, parallel_case *)
				case (instr_rdata_i[13:12])
					2'b00: data_type_o = 2'b10;
					2'b01: data_type_o = 2'b01;
					2'b10: data_type_o = 2'b00;
					default: begin
						data_req = 1'b0;
						data_we_o = 1'b0;
						illegal_insn_o = 1'b1;
					end
				endcase
			end
			zeroriscy_defines_OPCODE_LOAD: begin
				data_req = 1'b1;
				regfile_we = 1'b1;
				data_type_o = 2'b00;
				alu_operator_o = zeroriscy_defines_ALU_ADD;
				alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
				imm_b_mux_sel_o = zeroriscy_defines_IMMB_I;
				data_sign_extension_o = ~instr_rdata_i[14];
				(* full_case, parallel_case *)
				case (instr_rdata_i[13:12])
					2'b00: data_type_o = 2'b10;
					2'b01: data_type_o = 2'b01;
					2'b10: data_type_o = 2'b00;
					default: data_type_o = 2'b00;
				endcase
				if (instr_rdata_i[14:12] == 3'b111) begin
					alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_REGB_OR_FWD;
					data_sign_extension_o = ~instr_rdata_i[30];
					(* full_case, parallel_case *)
					case (instr_rdata_i[31:25])
						7'b0000000, 7'b0100000: data_type_o = 2'b10;
						7'b0001000, 7'b0101000: data_type_o = 2'b01;
						7'b0010000: data_type_o = 2'b00;
						default: illegal_insn_o = 1'b1;
					endcase
				end
				if (instr_rdata_i[14:12] == 3'b110)
					data_load_event_o = 1'b1;
				if (instr_rdata_i[14:12] == 3'b011)
					illegal_insn_o = 1'b1;
			end
			zeroriscy_defines_OPCODE_LUI: begin
				alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_IMM;
				alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
				imm_a_mux_sel_o = zeroriscy_defines_IMMA_ZERO;
				imm_b_mux_sel_o = zeroriscy_defines_IMMB_U;
				alu_operator_o = zeroriscy_defines_ALU_ADD;
				regfile_we = 1'b1;
			end
			zeroriscy_defines_OPCODE_AUIPC: begin
				alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_CURRPC;
				alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
				imm_b_mux_sel_o = zeroriscy_defines_IMMB_U;
				alu_operator_o = zeroriscy_defines_ALU_ADD;
				regfile_we = 1'b1;
			end
			zeroriscy_defines_OPCODE_OPIMM: begin
				alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
				imm_b_mux_sel_o = zeroriscy_defines_IMMB_I;
				regfile_we = 1'b1;
				(* full_case, parallel_case *)
				case (instr_rdata_i[14:12])
					3'b000: alu_operator_o = zeroriscy_defines_ALU_ADD;
					3'b010: alu_operator_o = zeroriscy_defines_ALU_SLTS;
					3'b011: alu_operator_o = zeroriscy_defines_ALU_SLTU;
					3'b100: alu_operator_o = zeroriscy_defines_ALU_XOR;
					3'b110: alu_operator_o = zeroriscy_defines_ALU_OR;
					3'b111: alu_operator_o = zeroriscy_defines_ALU_AND;
					3'b001: begin
						alu_operator_o = zeroriscy_defines_ALU_SLL;
						if (instr_rdata_i[31:25] != 7'b0000000)
							illegal_insn_o = 1'b1;
					end
					3'b101:
						if (instr_rdata_i[31:25] == 7'b0000000)
							alu_operator_o = zeroriscy_defines_ALU_SRL;
						else if (instr_rdata_i[31:25] == 7'b0100000)
							alu_operator_o = zeroriscy_defines_ALU_SRA;
						else
							illegal_insn_o = 1'b1;
					default: illegal_insn_o = 1'b1;
				endcase
			end
			zeroriscy_defines_OPCODE_OP: begin
				regfile_we = 1'b1;
				if (instr_rdata_i[31])
					illegal_insn_o = 1'b1;
				else if (~instr_rdata_i[28])
					(* full_case, parallel_case *)
					case ({instr_rdata_i[30:25], instr_rdata_i[14:12]})
						9'b000000000: alu_operator_o = zeroriscy_defines_ALU_ADD;
						9'b100000000: alu_operator_o = zeroriscy_defines_ALU_SUB;
						9'b000000010: alu_operator_o = zeroriscy_defines_ALU_SLTS;
						9'b000000011: alu_operator_o = zeroriscy_defines_ALU_SLTU;
						9'b000000100: alu_operator_o = zeroriscy_defines_ALU_XOR;
						9'b000000110: alu_operator_o = zeroriscy_defines_ALU_OR;
						9'b000000111: alu_operator_o = zeroriscy_defines_ALU_AND;
						9'b000000001: alu_operator_o = zeroriscy_defines_ALU_SLL;
						9'b000000101: alu_operator_o = zeroriscy_defines_ALU_SRL;
						9'b100000101: alu_operator_o = zeroriscy_defines_ALU_SRA;
						9'b000001000: begin
							alu_operator_o = zeroriscy_defines_ALU_ADD;
							multdiv_operator_o = zeroriscy_defines_MD_OP_MULL;
							mult_int_en = 1'b1;
							multdiv_signed_mode_o = 2'b00;
							illegal_insn_o = (RV32M ? 1'b0 : 1'b1);
						end
						9'b000001001: begin
							alu_operator_o = zeroriscy_defines_ALU_ADD;
							multdiv_operator_o = zeroriscy_defines_MD_OP_MULH;
							mult_int_en = 1'b1;
							multdiv_signed_mode_o = 2'b11;
							illegal_insn_o = (RV32M ? 1'b0 : 1'b1);
						end
						9'b000001010: begin
							alu_operator_o = zeroriscy_defines_ALU_ADD;
							multdiv_operator_o = zeroriscy_defines_MD_OP_MULH;
							mult_int_en = 1'b1;
							multdiv_signed_mode_o = 2'b01;
							illegal_insn_o = (RV32M ? 1'b0 : 1'b1);
						end
						9'b000001011: begin
							alu_operator_o = zeroriscy_defines_ALU_ADD;
							multdiv_operator_o = zeroriscy_defines_MD_OP_MULH;
							mult_int_en = 1'b1;
							multdiv_signed_mode_o = 2'b00;
							illegal_insn_o = (RV32M ? 1'b0 : 1'b1);
						end
						9'b000001100: begin
							alu_operator_o = zeroriscy_defines_ALU_ADD;
							multdiv_operator_o = zeroriscy_defines_MD_OP_DIV;
							div_int_en = 1'b1;
							multdiv_signed_mode_o = 2'b11;
							illegal_insn_o = (RV32M ? 1'b0 : 1'b1);
						end
						9'b000001101: begin
							alu_operator_o = zeroriscy_defines_ALU_ADD;
							multdiv_operator_o = zeroriscy_defines_MD_OP_DIV;
							div_int_en = 1'b1;
							multdiv_signed_mode_o = 2'b00;
							illegal_insn_o = (RV32M ? 1'b0 : 1'b1);
						end
						9'b000001110: begin
							alu_operator_o = zeroriscy_defines_ALU_ADD;
							multdiv_operator_o = zeroriscy_defines_MD_OP_REM;
							div_int_en = 1'b1;
							multdiv_signed_mode_o = 2'b11;
							illegal_insn_o = (RV32M ? 1'b0 : 1'b1);
						end
						9'b000001111: begin
							alu_operator_o = zeroriscy_defines_ALU_ADD;
							multdiv_operator_o = zeroriscy_defines_MD_OP_REM;
							div_int_en = 1'b1;
							multdiv_signed_mode_o = 2'b00;
							illegal_insn_o = (RV32M ? 1'b0 : 1'b1);
						end
						default: illegal_insn_o = 1'b1;
					endcase
			end
			zeroriscy_defines_OPCODE_PPU_OP: begin
				ppu_en = 1'b1;
				regfile_we = 1'b1;
				$display("%t Op: %b", $time, instr_rdata_i[31:0]);
				(* full_case, parallel_case *)
				case ({instr_rdata_i[31:25], instr_rdata_i[14:12]})
					10'b1101010000: ppu_operator_o = zeroriscy_defines_PPU_ADD;
					10'b1101010001: ppu_operator_o = zeroriscy_defines_PPU_SUB;
					10'b1101010010: ppu_operator_o = zeroriscy_defines_PPU_MUL;
					10'b1101010100: ppu_operator_o = zeroriscy_defines_PPU_DIV;
					10'b1101100000: ppu_operator_o = zeroriscy_defines_FMADD_S;
					10'b1101101000: ppu_operator_o = zeroriscy_defines_FMADD_C;
					10'b1101000000: ppu_operator_o = zeroriscy_defines_FLOAT_TO_POSIT;
					10'b1101001000: ppu_operator_o = zeroriscy_defines_POSIT_TO_FLOAT;
					default: illegal_insn_o = 1'b1;
				endcase
			end
			zeroriscy_defines_OPCODE_PPU_OPIMM: begin
				ppu_en = 1'b1;
				ppu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
				imm_b_mux_sel_o = zeroriscy_defines_IMMB_I;
				regfile_we = 1'b1;
				(* full_case, parallel_case *)
				case (instr_rdata_i[14:12])
					3'b000: ppu_operator_o = zeroriscy_defines_PPU_ADD;
					3'b010: ppu_operator_o = zeroriscy_defines_PPU_SUB;
					3'b011: ppu_operator_o = zeroriscy_defines_PPU_MUL;
					3'b100: ppu_operator_o = zeroriscy_defines_PPU_DIV;
					default: illegal_insn_o = 1'b1;
				endcase
			end
			zeroriscy_defines_OPCODE_SYSTEM:
				if (instr_rdata_i[14:12] == 3'b000)
					(* full_case, parallel_case *)
					case (instr_rdata_i[31:20])
						12'h000: ecall_insn_o = 1'b1;
						12'h001: ebrk_insn_o = 1'b1;
						12'h302: mret_insn_o = 1'b1;
						12'h105: pipe_flush_o = 1'b1;
						default: illegal_insn_o = 1'b1;
					endcase
				else begin
					csr_access_o = 1'b1;
					regfile_we = 1'b1;
					alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
					imm_a_mux_sel_o = zeroriscy_defines_IMMA_Z;
					imm_b_mux_sel_o = zeroriscy_defines_IMMB_I;
					if (instr_rdata_i[14] == 1'b1)
						alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_IMM;
					else
						alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_REGA_OR_FWD;
					(* full_case, parallel_case *)
					case (instr_rdata_i[13:12])
						2'b01: csr_op = zeroriscy_defines_CSR_OP_WRITE;
						2'b10: csr_op = zeroriscy_defines_CSR_OP_SET;
						2'b11: csr_op = zeroriscy_defines_CSR_OP_CLEAR;
						default: csr_illegal = 1'b1;
					endcase
					if (~csr_illegal) begin
						if (instr_rdata_i[31:20] == 12'h300)
							csr_status_o = 1'b1;
					end
					illegal_insn_o = csr_illegal;
				end
			default: illegal_insn_o = 1'b1;
		endcase
		if (illegal_c_insn_i)
			illegal_insn_o = 1'b1;
		if (data_misaligned_i == 1'b1) begin
			alu_op_a_mux_sel_o = zeroriscy_defines_OP_A_REGA_OR_FWD;
			alu_op_b_mux_sel_o = zeroriscy_defines_OP_B_IMM;
			imm_b_mux_sel_o = zeroriscy_defines_IMMB_PCINCR;
			regfile_we = 1'b0;
		end
	end
	assign regfile_we_o = (deassert_we_i ? 1'b0 : regfile_we);
	assign mult_int_en_o = (RV32M ? (deassert_we_i ? 1'b0 : mult_int_en) : 1'b0);
	assign div_int_en_o = (RV32M ? (deassert_we_i ? 1'b0 : div_int_en) : 1'b0);
	assign ppu_en_o = (deassert_we_i ? 1'b0 : ppu_en);
	assign data_req_o = (deassert_we_i ? 1'b0 : data_req);
	assign csr_op_o = (deassert_we_i ? zeroriscy_defines_CSR_OP_NONE : csr_op);
	assign jump_in_id_o = (deassert_we_i ? 1'b0 : jump_in_id);
	assign branch_in_id_o = (deassert_we_i ? 1'b0 : branch_in_id);
	initial _sv2v_0 = 0;
endmodule
module cluster_clock_gating (
	clk_i,
	en_i,
	test_en_i,
	clk_o
);
	input wire clk_i;
	input wire en_i;
	input wire test_en_i;
	output wire clk_o;
	assign clk_o = clk_i;
endmodule
module zeroriscy_ex_block (
	clk,
	rst_n,
	ppu_operand_a_i,
	ppu_operand_b_i,
	ppu_operand_c_i,
	ppu_operator_i,
	ppu_en_i,
	ppu_result_o,
	alu_operator_i,
	multdiv_operator_i,
	mult_en_i,
	div_en_i,
	alu_operand_a_i,
	alu_operand_b_i,
	multdiv_signed_mode_i,
	multdiv_operand_a_i,
	multdiv_operand_b_i,
	alu_adder_result_ex_o,
	regfile_wdata_ex_o,
	jump_target_o,
	branch_decision_o,
	lsu_en_i,
	lsu_ready_ex_i,
	ex_ready_o
);
	reg _sv2v_0;
	parameter RV32M = 1;
	input wire clk;
	input wire rst_n;
	input wire [31:0] ppu_operand_a_i;
	input wire [31:0] ppu_operand_b_i;
	input wire [31:0] ppu_operand_c_i;
	localparam zeroriscy_defines_PPU_OP_WIDTH = 3;
	input wire [2:0] ppu_operator_i;
	input wire ppu_en_i;
	output wire [31:0] ppu_result_o;
	localparam zeroriscy_defines_ALU_OP_WIDTH = 6;
	input wire [5:0] alu_operator_i;
	input wire [1:0] multdiv_operator_i;
	input wire mult_en_i;
	input wire div_en_i;
	input wire [31:0] alu_operand_a_i;
	input wire [31:0] alu_operand_b_i;
	input wire [1:0] multdiv_signed_mode_i;
	input wire [31:0] multdiv_operand_a_i;
	input wire [31:0] multdiv_operand_b_i;
	output wire [31:0] alu_adder_result_ex_o;
	output wire [31:0] regfile_wdata_ex_o;
	output wire [31:0] jump_target_o;
	output wire branch_decision_o;
	input wire lsu_en_i;
	input wire lsu_ready_ex_i;
	output reg ex_ready_o;
	localparam MULT_TYPE = 1;
	wire [31:0] alu_result;
	wire [31:0] multdiv_result;
	wire [31:0] ppu_result;
	wire [32:0] multdiv_alu_operand_b;
	wire [32:0] multdiv_alu_operand_a;
	wire [33:0] alu_adder_result_ext;
	wire alu_cmp_result;
	wire alu_is_equal_result;
	wire multdiv_ready;
	wire multdiv_en_sel;
	wire multdiv_en;
	wire ppu_en;
	localparam zeroriscy_defines_PPU_NUM = 1;
	wire [0:0] ppu_ready_v;
	wire ppu_ready;
	generate
		if (RV32M) begin : genblk1
			assign multdiv_en_sel = div_en_i;
			assign multdiv_en = mult_en_i | div_en_i;
		end
		else begin : genblk1
			assign multdiv_en_sel = 1'b0;
			assign multdiv_en = 1'b0;
		end
	endgenerate
	assign ppu_en = ppu_en_i;
	assign regfile_wdata_ex_o = (multdiv_en ? multdiv_result : (ppu_en ? ppu_result : alu_result));
	assign branch_decision_o = alu_cmp_result;
	assign jump_target_o = alu_adder_result_ex_o;
	zeroriscy_alu alu_i(
		.operator_i(alu_operator_i),
		.operand_a_i(alu_operand_a_i),
		.operand_b_i(alu_operand_b_i),
		.multdiv_operand_a_i(multdiv_alu_operand_a),
		.multdiv_operand_b_i(multdiv_alu_operand_b),
		.multdiv_en_i(multdiv_en_sel),
		.adder_result_o(alu_adder_result_ex_o),
		.adder_result_ext_o(alu_adder_result_ext),
		.result_o(alu_result),
		.comparison_result_o(alu_cmp_result),
		.is_equal_result_o(alu_is_equal_result)
	);
	generate
		if (1) begin : multdiv_fast
			zeroriscy_multdiv_fast multdiv_i(
				.clk(clk),
				.rst_n(rst_n),
				.mult_en_i(mult_en_i),
				.div_en_i(div_en_i),
				.operator_i(multdiv_operator_i),
				.signed_mode_i(multdiv_signed_mode_i),
				.op_a_i(multdiv_operand_a_i),
				.op_b_i(multdiv_operand_b_i),
				.alu_operand_a_o(multdiv_alu_operand_a),
				.alu_operand_b_o(multdiv_alu_operand_b),
				.alu_adder_ext_i(alu_adder_result_ext),
				.alu_adder_i(alu_adder_result_ex_o),
				.equal_to_zero(alu_is_equal_result),
				.ready_o(multdiv_ready),
				.multdiv_result_o(multdiv_result)
			);
		end
	endgenerate
	genvar _gv_i_2;
	localparam zeroriscy_defines_MULTI_PPU = 0;
	generate
		if (1) begin : ppu_single
			ppu_top ppu_top_inst(
				.clk_i(clk),
				.rst_i(~rst_n),
				.in_valid_i(ppu_en_i),
				.operand1_i(ppu_operand_a_i),
				.operand2_i(ppu_operand_b_i),
				.operand3_i(ppu_operand_c_i),
				.op_i(ppu_operator_i),
				.result_o(ppu_result),
				.out_valid_o(ppu_ready)
			);
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (1'b1)
			multdiv_en: ex_ready_o = multdiv_ready;
			lsu_en_i: ex_ready_o = lsu_ready_ex_i;
			ppu_en_i: ex_ready_o = ppu_ready;
			default: ex_ready_o = 1'b1;
		endcase
	end
	always @(posedge clk) begin
		$display("ppu_valid_o: %b", ppu_ready);
		$display("ppu_en: %h", ppu_en_i);
		$display("ppu_result: %h", ppu_result);
	end
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_fetch_fifo (
	clk,
	rst_n,
	clear_i,
	in_addr_i,
	in_rdata_i,
	in_valid_i,
	in_ready_o,
	out_valid_o,
	out_ready_i,
	out_rdata_o,
	out_addr_o,
	out_valid_stored_o
);
	reg _sv2v_0;
	input wire clk;
	input wire rst_n;
	input wire clear_i;
	input wire [31:0] in_addr_i;
	input wire [31:0] in_rdata_i;
	input wire in_valid_i;
	output wire in_ready_o;
	output reg out_valid_o;
	input wire out_ready_i;
	output reg [31:0] out_rdata_o;
	output wire [31:0] out_addr_o;
	output reg out_valid_stored_o;
	localparam DEPTH = 3;
	reg [95:0] addr_n;
	reg [95:0] addr_int;
	reg [95:0] addr_Q;
	reg [95:0] rdata_n;
	reg [95:0] rdata_int;
	reg [95:0] rdata_Q;
	reg [2:0] valid_n;
	reg [2:0] valid_int;
	reg [2:0] valid_Q;
	wire [31:0] addr_next;
	wire [31:0] rdata;
	wire [31:0] rdata_unaligned;
	wire valid;
	wire valid_unaligned;
	wire aligned_is_compressed;
	wire unaligned_is_compressed;
	wire aligned_is_compressed_st;
	wire unaligned_is_compressed_st;
	assign rdata = (valid_Q[0] ? rdata_Q[0+:32] : in_rdata_i);
	assign valid = valid_Q[0] || in_valid_i;
	assign rdata_unaligned = (valid_Q[1] ? {rdata_Q[47-:16], rdata[31:16]} : {in_rdata_i[15:0], rdata[31:16]});
	assign valid_unaligned = valid_Q[1] || (valid_Q[0] && in_valid_i);
	assign unaligned_is_compressed = rdata[17:16] != 2'b11;
	assign aligned_is_compressed = rdata[1:0] != 2'b11;
	assign unaligned_is_compressed_st = rdata_Q[17-:2] != 2'b11;
	assign aligned_is_compressed_st = rdata_Q[1-:2] != 2'b11;
	always @(*) begin
		if (_sv2v_0)
			;
		if (out_addr_o[1]) begin
			out_rdata_o = rdata_unaligned;
			if (unaligned_is_compressed)
				out_valid_o = valid;
			else
				out_valid_o = valid_unaligned;
		end
		else begin
			out_rdata_o = rdata;
			out_valid_o = valid;
		end
	end
	assign out_addr_o = (valid_Q[0] ? addr_Q[0+:32] : in_addr_i);
	always @(*) begin
		if (_sv2v_0)
			;
		out_valid_stored_o = 1'b1;
		if (out_addr_o[1]) begin
			if (unaligned_is_compressed_st)
				out_valid_stored_o = 1'b1;
			else
				out_valid_stored_o = valid_Q[1];
		end
		else
			out_valid_stored_o = valid_Q[0];
	end
	assign in_ready_o = ~valid_Q[1];
	always @(*) begin : sv2v_autoblock_1
		reg [0:1] _sv2v_jump;
		_sv2v_jump = 2'b00;
		begin : sv2v_autoblock_2
			reg signed [31:0] j;
			if (_sv2v_0)
				;
			addr_int = addr_Q;
			rdata_int = rdata_Q;
			valid_int = valid_Q;
			if (in_valid_i) begin : sv2v_autoblock_3
				reg signed [31:0] _sv2v_value_on_break;
				for (j = 0; j < DEPTH; j = j + 1)
					if (_sv2v_jump < 2'b10) begin
						_sv2v_jump = 2'b00;
						if (~valid_Q[j]) begin
							addr_int[j * 32+:32] = in_addr_i;
							rdata_int[j * 32+:32] = in_rdata_i;
							valid_int[j] = 1'b1;
							_sv2v_jump = 2'b10;
						end
						_sv2v_value_on_break = j;
					end
				if (!(_sv2v_jump < 2'b10))
					j = _sv2v_value_on_break;
				if (_sv2v_jump != 2'b11)
					_sv2v_jump = 2'b00;
			end
		end
	end
	assign addr_next = {addr_int[31-:30], 2'b00} + 32'h00000004;
	always @(*) begin
		if (_sv2v_0)
			;
		addr_n = addr_int;
		rdata_n = rdata_int;
		valid_n = valid_int;
		if (out_ready_i && out_valid_o) begin
			if (addr_int[1]) begin
				if (unaligned_is_compressed)
					addr_n[0+:32] = {addr_next[31:2], 2'b00};
				else
					addr_n[0+:32] = {addr_next[31:2], 2'b10};
				rdata_n = {32'b00000000000000000000000000000000, rdata_int[32+:64]};
				valid_n = {1'b0, valid_int[2:1]};
			end
			else if (aligned_is_compressed)
				addr_n[0+:32] = {addr_int[31-:30], 2'b10};
			else begin
				addr_n[0+:32] = {addr_next[31:2], 2'b00};
				rdata_n = {32'b00000000000000000000000000000000, rdata_int[32+:64]};
				valid_n = {1'b0, valid_int[2:1]};
			end
		end
	end
	always @(posedge clk or negedge rst_n)
		if (rst_n == 1'b0) begin
			addr_Q <= {DEPTH {32'b00000000000000000000000000000000}};
			rdata_Q <= {DEPTH {32'b00000000000000000000000000000000}};
			valid_Q <= 1'sb0;
		end
		else if (clear_i)
			valid_Q <= 1'sb0;
		else begin
			addr_Q <= addr_n;
			rdata_Q <= rdata_n;
			valid_Q <= valid_n;
		end
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_id_stage (
	clk,
	rst_n,
	test_en_i,
	fetch_enable_i,
	ctrl_busy_o,
	core_ctrl_firstfetch_o,
	is_decoding_o,
	instr_valid_i,
	instr_rdata_i,
	instr_req_o,
	branch_in_ex_o,
	branch_decision_i,
	clear_instr_valid_o,
	pc_set_o,
	pc_mux_o,
	exc_pc_mux_o,
	illegal_c_insn_i,
	is_compressed_i,
	pc_id_i,
	halt_if_o,
	id_ready_o,
	ex_ready_i,
	id_valid_o,
	alu_operator_ex_o,
	alu_operand_a_ex_o,
	alu_operand_b_ex_o,
	ppu_en_ex_o,
	ppu_operator_ex_o,
	ppu_operand_a_ex_o,
	ppu_operand_b_ex_o,
	ppu_operand_c_ex_o,
	mult_en_ex_o,
	div_en_ex_o,
	multdiv_operator_ex_o,
	multdiv_signed_mode_ex_o,
	multdiv_operand_a_ex_o,
	multdiv_operand_b_ex_o,
	csr_access_ex_o,
	csr_op_ex_o,
	csr_cause_o,
	csr_save_if_o,
	csr_save_id_o,
	csr_restore_mret_id_o,
	csr_save_cause_o,
	data_req_ex_o,
	data_we_ex_o,
	data_type_ex_o,
	data_sign_ext_ex_o,
	data_reg_offset_ex_o,
	data_load_event_ex_o,
	data_wdata_ex_o,
	data_misaligned_i,
	misaligned_addr_i,
	irq_i,
	irq_id_i,
	m_irq_enable_i,
	irq_ack_o,
	irq_id_o,
	exc_cause_o,
	lsu_load_err_i,
	lsu_store_err_i,
	dbg_settings_i,
	dbg_req_i,
	dbg_ack_o,
	dbg_stall_i,
	dbg_trap_o,
	dbg_reg_rreq_i,
	dbg_reg_raddr_i,
	dbg_reg_rdata_o,
	dbg_reg_wreq_i,
	dbg_reg_waddr_i,
	dbg_reg_wdata_i,
	dbg_jump_req_i,
	regfile_wdata_lsu_i,
	regfile_wdata_ex_i,
	csr_rdata_i,
	perf_jump_o,
	perf_branch_o,
	perf_tbranch_o
);
	reg _sv2v_0;
	parameter RV32M = 1;
	parameter RV32E = 0;
	input wire clk;
	input wire rst_n;
	input wire test_en_i;
	input wire fetch_enable_i;
	output wire ctrl_busy_o;
	output wire core_ctrl_firstfetch_o;
	output wire is_decoding_o;
	input wire instr_valid_i;
	input wire [31:0] instr_rdata_i;
	output wire instr_req_o;
	output wire branch_in_ex_o;
	input wire branch_decision_i;
	output wire clear_instr_valid_o;
	output wire pc_set_o;
	output wire [2:0] pc_mux_o;
	output wire [1:0] exc_pc_mux_o;
	input wire illegal_c_insn_i;
	input wire is_compressed_i;
	input wire [31:0] pc_id_i;
	output wire halt_if_o;
	output wire id_ready_o;
	input wire ex_ready_i;
	output wire id_valid_o;
	localparam zeroriscy_defines_ALU_OP_WIDTH = 6;
	output wire [5:0] alu_operator_ex_o;
	output wire [31:0] alu_operand_a_ex_o;
	output wire [31:0] alu_operand_b_ex_o;
	output wire ppu_en_ex_o;
	localparam zeroriscy_defines_PPU_OP_WIDTH = 3;
	output wire [2:0] ppu_operator_ex_o;
	output wire [31:0] ppu_operand_a_ex_o;
	output wire [31:0] ppu_operand_b_ex_o;
	output wire [31:0] ppu_operand_c_ex_o;
	output wire mult_en_ex_o;
	output wire div_en_ex_o;
	output wire [1:0] multdiv_operator_ex_o;
	output wire [1:0] multdiv_signed_mode_ex_o;
	output wire [31:0] multdiv_operand_a_ex_o;
	output wire [31:0] multdiv_operand_b_ex_o;
	output wire csr_access_ex_o;
	output wire [1:0] csr_op_ex_o;
	output wire [5:0] csr_cause_o;
	output wire csr_save_if_o;
	output wire csr_save_id_o;
	output wire csr_restore_mret_id_o;
	output wire csr_save_cause_o;
	output wire data_req_ex_o;
	output wire data_we_ex_o;
	output wire [1:0] data_type_ex_o;
	output wire data_sign_ext_ex_o;
	output wire [1:0] data_reg_offset_ex_o;
	output wire data_load_event_ex_o;
	output wire [31:0] data_wdata_ex_o;
	input wire data_misaligned_i;
	input wire [31:0] misaligned_addr_i;
	input wire irq_i;
	input wire [4:0] irq_id_i;
	input wire m_irq_enable_i;
	output wire irq_ack_o;
	output wire [4:0] irq_id_o;
	output wire [5:0] exc_cause_o;
	input wire lsu_load_err_i;
	input wire lsu_store_err_i;
	localparam zeroriscy_defines_DBG_SETS_W = 6;
	input wire [5:0] dbg_settings_i;
	input wire dbg_req_i;
	output wire dbg_ack_o;
	input wire dbg_stall_i;
	output wire dbg_trap_o;
	input wire dbg_reg_rreq_i;
	input wire [4:0] dbg_reg_raddr_i;
	output wire [31:0] dbg_reg_rdata_o;
	input wire dbg_reg_wreq_i;
	input wire [4:0] dbg_reg_waddr_i;
	input wire [31:0] dbg_reg_wdata_i;
	input wire dbg_jump_req_i;
	input wire [31:0] regfile_wdata_lsu_i;
	input wire [31:0] regfile_wdata_ex_i;
	input wire [31:0] csr_rdata_i;
	output wire perf_jump_o;
	output reg perf_branch_o;
	output wire perf_tbranch_o;
	wire [31:0] instr;
	wire deassert_we;
	wire illegal_insn_dec;
	wire illegal_reg_rv32e;
	wire ebrk_insn;
	wire mret_insn_dec;
	wire ecall_insn_dec;
	wire pipe_flush_dec;
	wire branch_taken_ex;
	wire branch_in_id;
	reg branch_set_n;
	reg branch_set_q;
	reg branch_mux_dec;
	reg jump_set;
	reg jump_mux_dec;
	wire jump_in_id;
	reg instr_multicyle;
	reg load_stall;
	reg multdiv_stall;
	reg ppu_stall;
	reg branch_stall;
	reg jump_stall;
	wire halt_id;
	reg regfile_we;
	reg select_data_rf;
	wire [31:0] imm_i_type;
	wire [31:0] imm_iz_type;
	wire [31:0] imm_s_type;
	wire [31:0] imm_sb_type;
	wire [31:0] imm_u_type;
	wire [31:0] imm_uj_type;
	wire [31:0] imm_z_type;
	wire [31:0] imm_s2_type;
	wire [31:0] imm_bi_type;
	wire [31:0] imm_s3_type;
	wire [31:0] imm_vs_type;
	wire [31:0] imm_vu_type;
	reg [31:0] imm_a;
	reg [31:0] imm_b;
	wire irq_req_ctrl;
	wire [4:0] irq_id_ctrl;
	wire exc_ack;
	wire exc_kill;
	wire [4:0] regfile_addr_ra_id;
	wire [4:0] regfile_addr_rb_id;
	wire [4:0] regfile_addr_rc_id;
	wire [4:0] regfile_alu_waddr_id;
	wire regfile_we_id;
	wire [31:0] regfile_data_ra_id;
	wire [31:0] regfile_data_rb_id;
	wire [31:0] regfile_data_rc_id;
	wire [5:0] alu_operator;
	wire [2:0] alu_op_a_mux_sel;
	wire [2:0] alu_op_b_mux_sel;
	wire [0:0] imm_a_mux_sel;
	wire [3:0] imm_b_mux_sel;
	wire [2:0] ppu_operator;
	wire [2:0] ppu_op_a_mux_sel;
	wire [2:0] ppu_op_b_mux_sel;
	wire [2:0] ppu_op_c_mux_sel;
	wire ppu_en;
	wire mult_int_en;
	wire div_int_en;
	wire multdiv_int_en;
	wire [1:0] multdiv_operator;
	wire [1:0] multdiv_signed_mode;
	wire data_we_id;
	wire [1:0] data_type_id;
	wire data_sign_ext_id;
	wire [1:0] data_reg_offset_id;
	wire data_req_id;
	wire data_load_event_id;
	wire csr_access;
	wire [1:0] csr_op;
	wire csr_status;
	wire [1:0] operand_a_fw_mux_sel;
	reg [31:0] operand_a_fw_id;
	wire [31:0] operand_b_fw_id;
	wire [31:0] operand_c_fw_id;
	reg [31:0] operand_b;
	reg [31:0] alu_operand_a;
	wire [31:0] alu_operand_b;
	reg [31:0] ppu_operand_a;
	reg [31:0] ppu_operand_b;
	reg [31:0] ppu_operand_c;
	assign instr = instr_rdata_i;
	assign imm_i_type = {{20 {instr[31]}}, instr[31:20]};
	assign imm_iz_type = {20'b00000000000000000000, instr[31:20]};
	assign imm_s_type = {{20 {instr[31]}}, instr[31:25], instr[11:7]};
	assign imm_sb_type = {{19 {instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
	assign imm_u_type = {instr[31:12], 12'b000000000000};
	assign imm_uj_type = {{12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
	assign imm_z_type = {27'b000000000000000000000000000, instr[19:15]};
	assign imm_s2_type = {27'b000000000000000000000000000, instr[24:20]};
	assign imm_bi_type = {{27 {instr[24]}}, instr[24:20]};
	assign imm_s3_type = {27'b000000000000000000000000000, instr[29:25]};
	assign imm_vs_type = {{26 {instr[24]}}, instr[24:20], instr[25]};
	assign imm_vu_type = {26'b00000000000000000000000000, instr[24:20], instr[25]};
	assign regfile_addr_ra_id = instr[19:15];
	assign regfile_addr_rb_id = instr[24:20];
	assign regfile_addr_rc_id = instr[14:10];
	assign regfile_alu_waddr_id = instr[11:7];
	assign illegal_reg_rv32e = 1'b0;
	assign clear_instr_valid_o = id_ready_o | halt_id;
	assign branch_taken_ex = branch_in_id & branch_decision_i;
	localparam zeroriscy_defines_OP_A_CURRPC = 3'b001;
	localparam zeroriscy_defines_OP_A_IMM = 3'b010;
	localparam zeroriscy_defines_OP_A_REGA_OR_FWD = 3'b000;
	always @(*) begin : alu_operand_a_mux
		if (_sv2v_0)
			;
		case (alu_op_a_mux_sel)
			zeroriscy_defines_OP_A_REGA_OR_FWD: alu_operand_a = operand_a_fw_id;
			zeroriscy_defines_OP_A_CURRPC: alu_operand_a = pc_id_i;
			zeroriscy_defines_OP_A_IMM: alu_operand_a = imm_a;
			default: alu_operand_a = operand_a_fw_id;
		endcase
		case (ppu_op_a_mux_sel)
			zeroriscy_defines_OP_A_REGA_OR_FWD: ppu_operand_a = operand_a_fw_id;
			zeroriscy_defines_OP_A_CURRPC: ppu_operand_a = pc_id_i;
			zeroriscy_defines_OP_A_IMM: ppu_operand_a = imm_a;
			default: ppu_operand_a = operand_a_fw_id;
		endcase
	end
	localparam zeroriscy_defines_IMMA_Z = 1'b0;
	localparam zeroriscy_defines_IMMA_ZERO = 1'b1;
	always @(*) begin : immediate_a_mux
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (imm_a_mux_sel)
			zeroriscy_defines_IMMA_Z: imm_a = imm_z_type;
			zeroriscy_defines_IMMA_ZERO: imm_a = 1'sb0;
			default: imm_a = 1'sb0;
		endcase
	end
	localparam zeroriscy_defines_SEL_MISALIGNED = 2'b11;
	localparam zeroriscy_defines_SEL_REGFILE = 2'b00;
	always @(*) begin : operand_a_fw_mux
		if (_sv2v_0)
			;
		case (operand_a_fw_mux_sel)
			zeroriscy_defines_SEL_MISALIGNED: operand_a_fw_id = misaligned_addr_i;
			zeroriscy_defines_SEL_REGFILE: operand_a_fw_id = regfile_data_ra_id;
			default: operand_a_fw_id = regfile_data_ra_id;
		endcase
	end
	localparam zeroriscy_defines_IMMB_BI = 4'b1011;
	localparam zeroriscy_defines_IMMB_I = 4'b0000;
	localparam zeroriscy_defines_IMMB_PCINCR = 4'b0011;
	localparam zeroriscy_defines_IMMB_S = 4'b0001;
	localparam zeroriscy_defines_IMMB_S2 = 4'b0100;
	localparam zeroriscy_defines_IMMB_S3 = 4'b0101;
	localparam zeroriscy_defines_IMMB_SB = 4'b1101;
	localparam zeroriscy_defines_IMMB_U = 4'b0010;
	localparam zeroriscy_defines_IMMB_UJ = 4'b1100;
	localparam zeroriscy_defines_IMMB_VS = 4'b0110;
	localparam zeroriscy_defines_IMMB_VU = 4'b0111;
	always @(*) begin : immediate_b_mux
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (imm_b_mux_sel)
			zeroriscy_defines_IMMB_I: imm_b = imm_i_type;
			zeroriscy_defines_IMMB_S: imm_b = imm_s_type;
			zeroriscy_defines_IMMB_U: imm_b = imm_u_type;
			zeroriscy_defines_IMMB_PCINCR: imm_b = (is_compressed_i && ~data_misaligned_i ? 32'h00000002 : 32'h00000004);
			zeroriscy_defines_IMMB_S2: imm_b = imm_s2_type;
			zeroriscy_defines_IMMB_BI: imm_b = imm_bi_type;
			zeroriscy_defines_IMMB_S3: imm_b = imm_s3_type;
			zeroriscy_defines_IMMB_VS: imm_b = imm_vs_type;
			zeroriscy_defines_IMMB_VU: imm_b = imm_vu_type;
			zeroriscy_defines_IMMB_UJ: imm_b = imm_uj_type;
			zeroriscy_defines_IMMB_SB: imm_b = imm_sb_type;
			default: imm_b = imm_i_type;
		endcase
	end
	localparam zeroriscy_defines_OP_B_IMM = 3'b010;
	localparam zeroriscy_defines_OP_B_REGB_OR_FWD = 3'b000;
	localparam zeroriscy_defines_POSIT_TO_FLOAT = 3'd7;
	always @(*) begin : alu_operand_b_mux
		if (_sv2v_0)
			;
		case (alu_op_b_mux_sel)
			zeroriscy_defines_OP_B_REGB_OR_FWD: operand_b = regfile_data_rb_id;
			zeroriscy_defines_OP_B_IMM: operand_b = imm_b;
			default: operand_b = regfile_data_rb_id;
		endcase
		case (ppu_op_b_mux_sel)
			zeroriscy_defines_OP_B_REGB_OR_FWD: ppu_operand_b = (ppu_operator == zeroriscy_defines_POSIT_TO_FLOAT ? ppu_operand_a : regfile_data_rb_id);
			zeroriscy_defines_OP_B_IMM: ppu_operand_b = imm_b;
			default: ppu_operand_b = regfile_data_rb_id;
		endcase
	end
	assign alu_operand_b = operand_b;
	assign operand_b_fw_id = regfile_data_rb_id;
	localparam zeroriscy_defines_FMADD_C = 3'd5;
	localparam zeroriscy_defines_FMADD_S = 3'd4;
	always @(*) begin : ppu_operand_c_mux
		if (_sv2v_0)
			;
		case (ppu_op_c_mux_sel)
			zeroriscy_defines_FMADD_S: ppu_operand_c = regfile_data_rc_id;
			zeroriscy_defines_FMADD_C: ppu_operand_c = regfile_data_rc_id;
			default: ppu_operand_c = 1'sb0;
		endcase
	end
	reg [31:0] regfile_wdata_mux;
	reg regfile_we_mux;
	reg [4:0] regfile_waddr_mux;
	always @(*) begin
		if (_sv2v_0)
			;
		if (dbg_reg_wreq_i) begin
			regfile_wdata_mux = dbg_reg_wdata_i;
			regfile_waddr_mux = dbg_reg_waddr_i;
			regfile_we_mux = 1'b1;
		end
		else begin
			regfile_we_mux = regfile_we;
			regfile_waddr_mux = regfile_alu_waddr_id;
			if (select_data_rf == 1'd0)
				regfile_wdata_mux = regfile_wdata_lsu_i;
			else if (csr_access)
				regfile_wdata_mux = csr_rdata_i;
			else
				regfile_wdata_mux = regfile_wdata_ex_i;
		end
	end
	zeroriscy_register_file #(.RV32E(RV32E)) registers_i(
		.clk(clk),
		.rst_n(rst_n),
		.test_en_i(test_en_i),
		.raddr_a_i(regfile_addr_ra_id),
		.rdata_a_o(regfile_data_ra_id),
		.raddr_b_i((dbg_reg_rreq_i == 1'b0 ? regfile_addr_rb_id : dbg_reg_raddr_i)),
		.rdata_b_o(regfile_data_rb_id),
		.raddr_c_i(regfile_addr_rc_id),
		.rdata_c_o(regfile_data_rc_id),
		.waddr_a_i(regfile_waddr_mux),
		.wdata_a_i(regfile_wdata_mux),
		.we_a_i(regfile_we_mux)
	);
	assign dbg_reg_rdata_o = regfile_data_rb_id;
	assign multdiv_int_en = mult_int_en | div_int_en;
	zeroriscy_decoder #(.RV32M(RV32M)) decoder_i(
		.deassert_we_i(deassert_we),
		.data_misaligned_i(data_misaligned_i),
		.branch_mux_i(branch_mux_dec),
		.jump_mux_i(jump_mux_dec),
		.illegal_insn_o(illegal_insn_dec),
		.ebrk_insn_o(ebrk_insn),
		.mret_insn_o(mret_insn_dec),
		.ecall_insn_o(ecall_insn_dec),
		.pipe_flush_o(pipe_flush_dec),
		.instr_rdata_i(instr),
		.illegal_c_insn_i(illegal_c_insn_i),
		.alu_operator_o(alu_operator),
		.alu_op_a_mux_sel_o(alu_op_a_mux_sel),
		.alu_op_b_mux_sel_o(alu_op_b_mux_sel),
		.imm_a_mux_sel_o(imm_a_mux_sel),
		.imm_b_mux_sel_o(imm_b_mux_sel),
		.mult_int_en_o(mult_int_en),
		.div_int_en_o(div_int_en),
		.multdiv_operator_o(multdiv_operator),
		.multdiv_signed_mode_o(multdiv_signed_mode),
		.ppu_operator_o(ppu_operator),
		.ppu_op_a_mux_sel_o(ppu_op_a_mux_sel),
		.ppu_op_b_mux_sel_o(ppu_op_b_mux_sel),
		.ppu_op_c_mux_sel_o(ppu_op_c_mux_sel),
		.ppu_en_o(ppu_en),
		.regfile_we_o(regfile_we_id),
		.csr_access_o(csr_access),
		.csr_op_o(csr_op),
		.csr_status_o(csr_status),
		.data_req_o(data_req_id),
		.data_we_o(data_we_id),
		.data_type_o(data_type_id),
		.data_sign_extension_o(data_sign_ext_id),
		.data_reg_offset_o(data_reg_offset_id),
		.data_load_event_o(data_load_event_id),
		.jump_in_id_o(jump_in_id),
		.branch_in_id_o(branch_in_id)
	);
	zeroriscy_controller controller_i(
		.clk(clk),
		.rst_n(rst_n),
		.fetch_enable_i(fetch_enable_i),
		.ctrl_busy_o(ctrl_busy_o),
		.first_fetch_o(core_ctrl_firstfetch_o),
		.is_decoding_o(is_decoding_o),
		.deassert_we_o(deassert_we),
		.illegal_insn_i(illegal_insn_dec | illegal_reg_rv32e),
		.ecall_insn_i(ecall_insn_dec),
		.mret_insn_i(mret_insn_dec),
		.pipe_flush_i(pipe_flush_dec),
		.ebrk_insn_i(ebrk_insn),
		.csr_status_i(csr_status),
		.instr_valid_i(instr_valid_i),
		.instr_req_o(instr_req_o),
		.pc_set_o(pc_set_o),
		.pc_mux_o(pc_mux_o),
		.exc_pc_mux_o(exc_pc_mux_o),
		.exc_cause_o(exc_cause_o),
		.data_misaligned_i(data_misaligned_i),
		.branch_in_id_i(branch_in_id),
		.branch_taken_ex_i(branch_taken_ex),
		.branch_set_i(branch_set_q),
		.jump_set_i(jump_set),
		.instr_multicyle_i(instr_multicyle),
		.irq_req_ctrl_i(irq_req_ctrl),
		.irq_id_ctrl_i(irq_id_ctrl),
		.m_IE_i(m_irq_enable_i),
		.irq_ack_o(irq_ack_o),
		.irq_id_o(irq_id_o),
		.exc_ack_o(exc_ack),
		.exc_kill_o(exc_kill),
		.csr_save_cause_o(csr_save_cause_o),
		.csr_cause_o(csr_cause_o),
		.csr_save_if_o(csr_save_if_o),
		.csr_save_id_o(csr_save_id_o),
		.csr_restore_mret_id_o(csr_restore_mret_id_o),
		.dbg_req_i(dbg_req_i),
		.dbg_ack_o(dbg_ack_o),
		.dbg_stall_i(dbg_stall_i),
		.dbg_jump_req_i(dbg_jump_req_i),
		.dbg_settings_i(dbg_settings_i),
		.dbg_trap_o(dbg_trap_o),
		.operand_a_fw_mux_sel_o(operand_a_fw_mux_sel),
		.halt_if_o(halt_if_o),
		.halt_id_o(halt_id),
		.id_ready_i(id_ready_o),
		.perf_jump_o(perf_jump_o),
		.perf_tbranch_o(perf_tbranch_o)
	);
	zeroriscy_int_controller int_controller_i(
		.clk(clk),
		.rst_n(rst_n),
		.irq_req_ctrl_o(irq_req_ctrl),
		.irq_id_ctrl_o(irq_id_ctrl),
		.ctrl_ack_i(exc_ack),
		.ctrl_kill_i(exc_kill),
		.irq_i(irq_i),
		.irq_id_i(irq_id_i),
		.m_IE_i(m_irq_enable_i)
	);
	assign data_we_ex_o = data_we_id;
	assign data_type_ex_o = data_type_id;
	assign data_sign_ext_ex_o = data_sign_ext_id;
	assign data_wdata_ex_o = regfile_data_rb_id;
	assign data_req_ex_o = data_req_id;
	assign data_reg_offset_ex_o = data_reg_offset_id;
	assign data_load_event_ex_o = data_load_event_id;
	assign alu_operator_ex_o = alu_operator;
	assign alu_operand_a_ex_o = alu_operand_a;
	assign alu_operand_b_ex_o = alu_operand_b;
	assign ppu_operator_ex_o = ppu_operator;
	assign ppu_operand_a_ex_o = ppu_operand_a;
	assign ppu_operand_b_ex_o = ppu_operand_b;
	assign ppu_operand_c_ex_o = ppu_operand_c;
	assign csr_access_ex_o = csr_access;
	assign csr_op_ex_o = csr_op;
	assign branch_in_ex_o = branch_in_id;
	assign mult_en_ex_o = mult_int_en;
	assign div_en_ex_o = div_int_en;
	assign ppu_en_ex_o = ppu_en;
	assign multdiv_operator_ex_o = multdiv_operator;
	assign multdiv_signed_mode_ex_o = multdiv_signed_mode;
	assign multdiv_operand_a_ex_o = regfile_data_ra_id;
	assign multdiv_operand_b_ex_o = regfile_data_rb_id;
	reg id_wb_fsm_cs;
	reg id_wb_fsm_ns;
	always @(posedge clk or negedge rst_n) begin : EX_WB_Pipeline_Register
		if (~rst_n) begin
			id_wb_fsm_cs <= 1'd0;
			branch_set_q <= 1'b0;
		end
		else begin
			id_wb_fsm_cs <= id_wb_fsm_ns;
			branch_set_q <= branch_set_n;
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		id_wb_fsm_ns = id_wb_fsm_cs;
		regfile_we = regfile_we_id;
		load_stall = 1'b0;
		multdiv_stall = 1'b0;
		ppu_stall = 1'b0;
		jump_stall = 1'b0;
		branch_stall = 1'b0;
		select_data_rf = 1'd1;
		instr_multicyle = 1'b0;
		branch_set_n = 1'b0;
		branch_mux_dec = 1'b0;
		jump_set = 1'b0;
		jump_mux_dec = 1'b0;
		perf_branch_o = 1'b0;
		(* full_case, parallel_case *)
		case (id_wb_fsm_cs)
			1'd0: begin
				jump_mux_dec = 1'b1;
				branch_mux_dec = 1'b1;
				(* full_case, parallel_case *)
				case (1'b1)
					data_req_id: begin
						regfile_we = 1'b0;
						id_wb_fsm_ns = 1'd1;
						load_stall = 1'b1;
						instr_multicyle = 1'b1;
					end
					branch_in_id: begin
						id_wb_fsm_ns = (branch_decision_i ? 1'd1 : 1'd0);
						branch_stall = branch_decision_i;
						instr_multicyle = branch_decision_i;
						branch_set_n = branch_decision_i;
						perf_branch_o = 1'b1;
					end
					multdiv_int_en: begin
						regfile_we = 1'b0;
						id_wb_fsm_ns = 1'd1;
						multdiv_stall = 1'b1;
						instr_multicyle = 1'b1;
					end
					ppu_en: begin
						regfile_we = 1'b0;
						id_wb_fsm_ns = 1'd1;
						ppu_stall = 1'b1;
						instr_multicyle = 1'b1;
					end
					jump_in_id: begin
						regfile_we = 1'b0;
						id_wb_fsm_ns = 1'd1;
						jump_stall = 1'b1;
						instr_multicyle = 1'b1;
						jump_set = 1'b1;
					end
					default:
						;
				endcase
			end
			1'd1:
				if (ex_ready_i) begin
					regfile_we = regfile_we_id;
					id_wb_fsm_ns = 1'd0;
					load_stall = 1'b0;
					multdiv_stall = 1'b0;
					ppu_stall = 1'b0;
					select_data_rf = (data_req_id ? 1'd0 : 1'd1);
				end
				else begin
					regfile_we = 1'b0;
					instr_multicyle = 1'b1;
					(* full_case, parallel_case *)
					case (1'b1)
						data_req_id: load_stall = 1'b1;
						multdiv_int_en: multdiv_stall = 1'b1;
						ppu_en: ppu_stall = 1'b1;
						default:
							;
					endcase
				end
			default:
				;
		endcase
	end
	assign id_ready_o = (((~load_stall & ~branch_stall) & ~jump_stall) & ~multdiv_stall) & ~ppu_stall;
	assign id_valid_o = ~halt_id & id_ready_o;
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_if_stage (
	clk,
	rst_n,
	boot_addr_i,
	req_i,
	instr_req_o,
	instr_addr_o,
	instr_gnt_i,
	instr_rvalid_i,
	instr_rdata_i,
	instr_valid_id_o,
	instr_rdata_id_o,
	is_compressed_id_o,
	illegal_c_insn_id_o,
	pc_if_o,
	pc_id_o,
	clear_instr_valid_i,
	pc_set_i,
	exception_pc_reg_i,
	pc_mux_i,
	exc_pc_mux_i,
	exc_vec_pc_mux_i,
	jump_target_ex_i,
	dbg_jump_addr_i,
	halt_if_i,
	id_ready_i,
	if_valid_o,
	if_busy_o,
	perf_imiss_o
);
	reg _sv2v_0;
	input wire clk;
	input wire rst_n;
	input wire [31:0] boot_addr_i;
	input wire req_i;
	output wire instr_req_o;
	output wire [31:0] instr_addr_o;
	input wire instr_gnt_i;
	input wire instr_rvalid_i;
	input wire [31:0] instr_rdata_i;
	output reg instr_valid_id_o;
	output reg [31:0] instr_rdata_id_o;
	output reg is_compressed_id_o;
	output reg illegal_c_insn_id_o;
	output wire [31:0] pc_if_o;
	output reg [31:0] pc_id_o;
	input wire clear_instr_valid_i;
	input wire pc_set_i;
	input wire [31:0] exception_pc_reg_i;
	input wire [2:0] pc_mux_i;
	input wire [1:0] exc_pc_mux_i;
	input wire [4:0] exc_vec_pc_mux_i;
	input wire [31:0] jump_target_ex_i;
	input wire [31:0] dbg_jump_addr_i;
	input wire halt_if_i;
	input wire id_ready_i;
	output wire if_valid_o;
	output wire if_busy_o;
	output wire perf_imiss_o;
	reg [0:0] offset_fsm_cs;
	reg [0:0] offset_fsm_ns;
	reg valid;
	wire if_ready;
	wire prefetch_busy;
	reg branch_req;
	reg [31:0] fetch_addr_n;
	wire fetch_valid;
	reg fetch_ready;
	wire [31:0] fetch_rdata;
	wire [31:0] fetch_addr;
	reg [31:0] exc_pc;
	localparam zeroriscy_defines_EXC_OFF_ECALL = 8'h88;
	localparam zeroriscy_defines_EXC_OFF_ILLINSN = 8'h84;
	localparam zeroriscy_defines_EXC_PC_ECALL = 2'b01;
	localparam zeroriscy_defines_EXC_PC_ILLINSN = 2'b00;
	localparam zeroriscy_defines_EXC_PC_IRQ = 2'b11;
	always @(*) begin : EXC_PC_MUX
		if (_sv2v_0)
			;
		exc_pc = 1'sb0;
		(* full_case, parallel_case *)
		case (exc_pc_mux_i)
			zeroriscy_defines_EXC_PC_ILLINSN: exc_pc = {boot_addr_i[31:8], zeroriscy_defines_EXC_OFF_ILLINSN};
			zeroriscy_defines_EXC_PC_ECALL: exc_pc = {boot_addr_i[31:8], zeroriscy_defines_EXC_OFF_ECALL};
			zeroriscy_defines_EXC_PC_IRQ: exc_pc = {boot_addr_i[31:8], 1'b0, exc_vec_pc_mux_i[4:0], 2'b00};
			default:
				;
		endcase
	end
	localparam zeroriscy_defines_EXC_OFF_RST = 8'h80;
	localparam zeroriscy_defines_PC_BOOT = 3'b000;
	localparam zeroriscy_defines_PC_DBG_NPC = 3'b111;
	localparam zeroriscy_defines_PC_ERET = 3'b101;
	localparam zeroriscy_defines_PC_EXCEPTION = 3'b100;
	localparam zeroriscy_defines_PC_JUMP = 3'b010;
	always @(*) begin
		if (_sv2v_0)
			;
		fetch_addr_n = 1'sb0;
		(* full_case, parallel_case *)
		case (pc_mux_i)
			zeroriscy_defines_PC_BOOT: fetch_addr_n = {boot_addr_i[31:8], zeroriscy_defines_EXC_OFF_RST};
			zeroriscy_defines_PC_JUMP: fetch_addr_n = jump_target_ex_i;
			zeroriscy_defines_PC_EXCEPTION: fetch_addr_n = exc_pc;
			zeroriscy_defines_PC_ERET: fetch_addr_n = exception_pc_reg_i;
			zeroriscy_defines_PC_DBG_NPC: fetch_addr_n = dbg_jump_addr_i;
			default:
				;
		endcase
	end
	zeroriscy_prefetch_buffer prefetch_buffer_i(
		.clk(clk),
		.rst_n(rst_n),
		.req_i(req_i),
		.branch_i(branch_req),
		.addr_i({fetch_addr_n[31:1], 1'b0}),
		.ready_i(fetch_ready),
		.valid_o(fetch_valid),
		.rdata_o(fetch_rdata),
		.addr_o(fetch_addr),
		.instr_req_o(instr_req_o),
		.instr_addr_o(instr_addr_o),
		.instr_gnt_i(instr_gnt_i),
		.instr_rvalid_i(instr_rvalid_i),
		.instr_rdata_i(instr_rdata_i),
		.busy_o(prefetch_busy)
	);
	always @(posedge clk or negedge rst_n)
		if (rst_n == 1'b0)
			offset_fsm_cs <= 1'd1;
		else
			offset_fsm_cs <= offset_fsm_ns;
	always @(*) begin
		if (_sv2v_0)
			;
		offset_fsm_ns = offset_fsm_cs;
		fetch_ready = 1'b0;
		branch_req = 1'b0;
		valid = 1'b0;
		(* full_case, parallel_case *)
		case (offset_fsm_cs)
			1'd1:
				if (req_i) begin
					branch_req = 1'b1;
					offset_fsm_ns = 1'd0;
				end
			1'd0:
				if (fetch_valid) begin
					valid = 1'b1;
					if (req_i && if_valid_o) begin
						fetch_ready = 1'b1;
						offset_fsm_ns = 1'd0;
					end
				end
			default: offset_fsm_ns = 1'd1;
		endcase
		if (pc_set_i) begin
			valid = 1'b0;
			branch_req = 1'b1;
			offset_fsm_ns = 1'd0;
		end
	end
	assign pc_if_o = fetch_addr;
	assign if_busy_o = prefetch_busy;
	assign perf_imiss_o = ~fetch_valid | branch_req;
	wire [31:0] instr_decompressed;
	wire illegal_c_insn;
	wire instr_compressed_int;
	zeroriscy_compressed_decoder compressed_decoder_i(
		.instr_i(fetch_rdata),
		.instr_o(instr_decompressed),
		.is_compressed_o(instr_compressed_int),
		.illegal_instr_o(illegal_c_insn)
	);
	always @(posedge clk or negedge rst_n) begin : IF_ID_PIPE_REGISTERS
		if (rst_n == 1'b0) begin
			instr_valid_id_o <= 1'b0;
			instr_rdata_id_o <= 1'sb0;
			illegal_c_insn_id_o <= 1'b0;
			is_compressed_id_o <= 1'b0;
			pc_id_o <= 1'sb0;
		end
		else if (if_valid_o) begin
			instr_valid_id_o <= 1'b1;
			instr_rdata_id_o <= instr_decompressed;
			illegal_c_insn_id_o <= illegal_c_insn;
			is_compressed_id_o <= instr_compressed_int;
			pc_id_o <= pc_if_o;
		end
		else if (clear_instr_valid_i)
			instr_valid_id_o <= 1'b0;
	end
	assign if_ready = valid & id_ready_i;
	assign if_valid_o = ~halt_if_i & if_ready;
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_int_controller (
	clk,
	rst_n,
	irq_req_ctrl_o,
	irq_id_ctrl_o,
	ctrl_ack_i,
	ctrl_kill_i,
	irq_i,
	irq_id_i,
	m_IE_i
);
	input wire clk;
	input wire rst_n;
	output wire irq_req_ctrl_o;
	output wire [4:0] irq_id_ctrl_o;
	input wire ctrl_ack_i;
	input wire ctrl_kill_i;
	input wire irq_i;
	input wire [4:0] irq_id_i;
	input wire m_IE_i;
	reg [1:0] exc_ctrl_cs;
	wire [1:0] exc_ctrl_ns;
	wire irq_enable_ext;
	reg [4:0] irq_id_q;
	assign irq_enable_ext = m_IE_i;
	assign irq_req_ctrl_o = exc_ctrl_cs == 2'd1;
	assign irq_id_ctrl_o = irq_id_q;
	always @(posedge clk or negedge rst_n)
		if (rst_n == 1'b0) begin
			irq_id_q <= 1'sb0;
			exc_ctrl_cs <= 2'd0;
		end
		else
			(* full_case, parallel_case *)
			case (exc_ctrl_cs)
				2'd0:
					if (irq_enable_ext & irq_i) begin
						exc_ctrl_cs <= 2'd1;
						irq_id_q <= irq_id_i;
					end
				2'd1:
					(* full_case, parallel_case *)
					case (1'b1)
						ctrl_ack_i: exc_ctrl_cs <= 2'd2;
						ctrl_kill_i: exc_ctrl_cs <= 2'd0;
						default: exc_ctrl_cs <= 2'd1;
					endcase
				2'd2: exc_ctrl_cs <= 2'd0;
			endcase
endmodule
module zeroriscy_load_store_unit (
	clk,
	rst_n,
	data_req_o,
	data_gnt_i,
	data_rvalid_i,
	data_err_i,
	data_addr_o,
	data_we_o,
	data_be_o,
	data_wdata_o,
	data_rdata_i,
	data_we_ex_i,
	data_type_ex_i,
	data_wdata_ex_i,
	data_reg_offset_ex_i,
	data_sign_ext_ex_i,
	data_rdata_ex_o,
	data_req_ex_i,
	adder_result_ex_i,
	ppu_result_ex_i,
	data_misaligned_o,
	misaligned_addr_o,
	load_err_o,
	store_err_o,
	lsu_update_addr_o,
	data_valid_o,
	busy_o
);
	reg _sv2v_0;
	input wire clk;
	input wire rst_n;
	output reg data_req_o;
	input wire data_gnt_i;
	input wire data_rvalid_i;
	input wire data_err_i;
	output wire [31:0] data_addr_o;
	output wire data_we_o;
	output wire [3:0] data_be_o;
	output wire [31:0] data_wdata_o;
	input wire [31:0] data_rdata_i;
	input wire data_we_ex_i;
	input wire [1:0] data_type_ex_i;
	input wire [31:0] data_wdata_ex_i;
	input wire [1:0] data_reg_offset_ex_i;
	input wire data_sign_ext_ex_i;
	output wire [31:0] data_rdata_ex_o;
	input wire data_req_ex_i;
	input wire [31:0] adder_result_ex_i;
	input wire [31:0] ppu_result_ex_i;
	output reg data_misaligned_o;
	output reg [31:0] misaligned_addr_o;
	output wire load_err_o;
	output wire store_err_o;
	output reg lsu_update_addr_o;
	output reg data_valid_o;
	output wire busy_o;
	wire [31:0] data_addr_int;
	reg [1:0] data_type_q;
	reg [1:0] rdata_offset_q;
	reg data_sign_ext_q;
	reg data_we_q;
	wire [1:0] wdata_offset;
	reg [3:0] data_be;
	reg [31:0] data_wdata;
	wire misaligned_st;
	reg data_misaligned;
	reg data_misaligned_q;
	reg increase_address;
	reg [2:0] CS;
	reg [2:0] NS;
	reg [31:0] rdata_q;
	always @(*) begin
		if (_sv2v_0)
			;
		case (data_type_ex_i)
			2'b00:
				if (misaligned_st == 1'b0)
					case (data_addr_int[1:0])
						2'b00: data_be = 4'b1111;
						2'b01: data_be = 4'b1110;
						2'b10: data_be = 4'b1100;
						2'b11: data_be = 4'b1000;
					endcase
				else
					case (data_addr_int[1:0])
						2'b00: data_be = 4'b0000;
						2'b01: data_be = 4'b0001;
						2'b10: data_be = 4'b0011;
						2'b11: data_be = 4'b0111;
					endcase
			2'b01:
				if (misaligned_st == 1'b0)
					case (data_addr_int[1:0])
						2'b00: data_be = 4'b0011;
						2'b01: data_be = 4'b0110;
						2'b10: data_be = 4'b1100;
						2'b11: data_be = 4'b1000;
					endcase
				else
					data_be = 4'b0001;
			2'b10, 2'b11:
				case (data_addr_int[1:0])
					2'b00: data_be = 4'b0001;
					2'b01: data_be = 4'b0010;
					2'b10: data_be = 4'b0100;
					2'b11: data_be = 4'b1000;
				endcase
		endcase
	end
	assign wdata_offset = data_addr_int[1:0] - data_reg_offset_ex_i[1:0];
	always @(*) begin
		if (_sv2v_0)
			;
		case (wdata_offset)
			2'b00: data_wdata = data_wdata_ex_i[31:0];
			2'b01: data_wdata = {data_wdata_ex_i[23:0], data_wdata_ex_i[31:24]};
			2'b10: data_wdata = {data_wdata_ex_i[15:0], data_wdata_ex_i[31:16]};
			2'b11: data_wdata = {data_wdata_ex_i[7:0], data_wdata_ex_i[31:8]};
		endcase
	end
	always @(posedge clk or negedge rst_n)
		if (rst_n == 1'b0) begin
			data_type_q <= 1'sb0;
			rdata_offset_q <= 1'sb0;
			data_sign_ext_q <= 1'sb0;
			data_we_q <= 1'b0;
		end
		else if (data_gnt_i == 1'b1) begin
			data_type_q <= data_type_ex_i;
			rdata_offset_q <= data_addr_int[1:0];
			data_sign_ext_q <= data_sign_ext_ex_i;
			data_we_q <= data_we_ex_i;
		end
	reg [31:0] data_rdata_ext;
	reg [31:0] rdata_w_ext;
	reg [31:0] rdata_h_ext;
	reg [31:0] rdata_b_ext;
	always @(*) begin
		if (_sv2v_0)
			;
		case (rdata_offset_q)
			2'b00: rdata_w_ext = data_rdata_i[31:0];
			2'b01: rdata_w_ext = {data_rdata_i[7:0], rdata_q[31:8]};
			2'b10: rdata_w_ext = {data_rdata_i[15:0], rdata_q[31:16]};
			2'b11: rdata_w_ext = {data_rdata_i[23:0], rdata_q[31:24]};
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		case (rdata_offset_q)
			2'b00:
				if (data_sign_ext_q == 1'b0)
					rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
				else
					rdata_h_ext = {{16 {data_rdata_i[15]}}, data_rdata_i[15:0]};
			2'b01:
				if (data_sign_ext_q == 1'b0)
					rdata_h_ext = {16'h0000, data_rdata_i[23:8]};
				else
					rdata_h_ext = {{16 {data_rdata_i[23]}}, data_rdata_i[23:8]};
			2'b10:
				if (data_sign_ext_q == 1'b0)
					rdata_h_ext = {16'h0000, data_rdata_i[31:16]};
				else
					rdata_h_ext = {{16 {data_rdata_i[31]}}, data_rdata_i[31:16]};
			2'b11:
				if (data_sign_ext_q == 1'b0)
					rdata_h_ext = {16'h0000, data_rdata_i[7:0], rdata_q[31:24]};
				else
					rdata_h_ext = {{16 {data_rdata_i[7]}}, data_rdata_i[7:0], rdata_q[31:24]};
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		case (rdata_offset_q)
			2'b00:
				if (data_sign_ext_q == 1'b0)
					rdata_b_ext = {24'h000000, data_rdata_i[7:0]};
				else
					rdata_b_ext = {{24 {data_rdata_i[7]}}, data_rdata_i[7:0]};
			2'b01:
				if (data_sign_ext_q == 1'b0)
					rdata_b_ext = {24'h000000, data_rdata_i[15:8]};
				else
					rdata_b_ext = {{24 {data_rdata_i[15]}}, data_rdata_i[15:8]};
			2'b10:
				if (data_sign_ext_q == 1'b0)
					rdata_b_ext = {24'h000000, data_rdata_i[23:16]};
				else
					rdata_b_ext = {{24 {data_rdata_i[23]}}, data_rdata_i[23:16]};
			2'b11:
				if (data_sign_ext_q == 1'b0)
					rdata_b_ext = {24'h000000, data_rdata_i[31:24]};
				else
					rdata_b_ext = {{24 {data_rdata_i[31]}}, data_rdata_i[31:24]};
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		case (data_type_q)
			2'b00: data_rdata_ext = rdata_w_ext;
			2'b01: data_rdata_ext = rdata_h_ext;
			2'b10, 2'b11: data_rdata_ext = rdata_b_ext;
		endcase
	end
	always @(posedge clk or negedge rst_n)
		if (rst_n == 1'b0) begin
			CS <= 3'd0;
			rdata_q <= 1'sb0;
			data_misaligned_q <= 1'sb0;
			misaligned_addr_o <= 32'b00000000000000000000000000000000;
		end
		else begin
			CS <= NS;
			if (lsu_update_addr_o) begin
				data_misaligned_q <= data_misaligned;
				if (increase_address)
					misaligned_addr_o <= data_addr_int;
			end
			if (data_rvalid_i && ~data_we_q) begin
				if ((data_misaligned_q == 1'b1) || (data_misaligned == 1'b1))
					rdata_q <= data_rdata_i;
				else
					rdata_q <= data_rdata_ext;
			end
		end
	assign data_rdata_ex_o = (data_rvalid_i == 1'b1 ? data_rdata_ext : rdata_q);
	assign data_addr_o = data_addr_int;
	assign data_wdata_o = data_wdata;
	assign data_we_o = data_we_ex_i;
	assign data_be_o = data_be;
	assign misaligned_st = data_misaligned_q;
	assign load_err_o = 1'b0;
	assign store_err_o = 1'b0;
	always @(*) begin
		if (_sv2v_0)
			;
		NS = CS;
		data_req_o = 1'b0;
		lsu_update_addr_o = 1'b0;
		data_valid_o = 1'b0;
		increase_address = 1'b0;
		data_misaligned_o = 1'b0;
		case (CS)
			3'd0:
				if (data_req_ex_i) begin
					data_req_o = data_req_ex_i;
					if (data_gnt_i) begin
						lsu_update_addr_o = 1'b1;
						increase_address = data_misaligned;
						NS = (data_misaligned ? 3'd2 : 3'd4);
					end
					else
						NS = (data_misaligned ? 3'd1 : 3'd3);
				end
			3'd1: begin
				data_req_o = 1'b1;
				if (data_gnt_i) begin
					lsu_update_addr_o = 1'b1;
					increase_address = data_misaligned;
					NS = 3'd2;
				end
			end
			3'd2: begin
				increase_address = 1'b0;
				data_misaligned_o = 1'b1;
				data_req_o = 1'b0;
				lsu_update_addr_o = data_gnt_i;
				if (data_rvalid_i) begin
					data_req_o = 1'b1;
					if (data_gnt_i)
						NS = 3'd4;
					else
						NS = 3'd3;
				end
				else
					NS = 3'd2;
			end
			3'd3: begin
				data_misaligned_o = data_misaligned_q;
				data_req_o = 1'b1;
				if (data_gnt_i) begin
					lsu_update_addr_o = 1'b1;
					NS = 3'd4;
				end
			end
			3'd4: begin
				data_req_o = 1'b0;
				if (data_rvalid_i) begin
					data_valid_o = 1'b1;
					NS = 3'd0;
				end
				else
					NS = 3'd4;
			end
			default: NS = 3'd0;
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		data_misaligned = 1'b0;
		if ((data_req_ex_i == 1'b1) && (data_misaligned_q == 1'b0))
			case (data_type_ex_i)
				2'b00:
					if (data_addr_int[1:0] != 2'b00)
						data_misaligned = 1'b1;
				2'b01:
					if (data_addr_int[1:0] == 2'b11)
						data_misaligned = 1'b1;
				default:
					;
			endcase
	end
	assign data_addr_int = adder_result_ex_i;
	assign busy_o = (CS == 3'd4) || (data_req_o == 1'b1);
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_multdiv_fast (
	clk,
	rst_n,
	mult_en_i,
	div_en_i,
	operator_i,
	signed_mode_i,
	op_a_i,
	op_b_i,
	alu_adder_ext_i,
	alu_adder_i,
	equal_to_zero,
	alu_operand_a_o,
	alu_operand_b_o,
	multdiv_result_o,
	ready_o
);
	reg _sv2v_0;
	input wire clk;
	input wire rst_n;
	input wire mult_en_i;
	input wire div_en_i;
	input wire [1:0] operator_i;
	input wire [1:0] signed_mode_i;
	input wire [31:0] op_a_i;
	input wire [31:0] op_b_i;
	input wire [33:0] alu_adder_ext_i;
	input wire [31:0] alu_adder_i;
	input wire equal_to_zero;
	output reg [32:0] alu_operand_a_o;
	output reg [32:0] alu_operand_b_o;
	output wire [31:0] multdiv_result_o;
	output wire ready_o;
	reg [4:0] div_counter_q;
	reg [4:0] div_counter_n;
	reg [1:0] mult_state_q;
	reg [1:0] mult_state_n;
	reg [2:0] divcurr_state_q;
	reg [2:0] divcurr_state_n;
	wire [34:0] mac_res_ext;
	reg [33:0] mac_res_q;
	reg [33:0] mac_res_n;
	wire [33:0] mac_res;
	reg [33:0] op_reminder_n;
	reg [15:0] mult_op_a;
	reg [15:0] mult_op_b;
	reg [33:0] accum;
	reg sign_a;
	reg sign_b;
	wire div_sign_a;
	wire div_sign_b;
	wire signed_mult;
	reg is_greater_equal;
	wire div_change_sign;
	wire rem_change_sign;
	wire [31:0] one_shift;
	reg [31:0] op_denominator_q;
	reg [31:0] op_numerator_q;
	reg [31:0] op_quotient_q;
	reg [31:0] op_denominator_n;
	reg [31:0] op_numerator_n;
	reg [31:0] op_quotient_n;
	wire [32:0] next_reminder;
	wire [32:0] next_quotient;
	wire [32:0] res_adder_h;
	reg mult_is_ready;
	always @(posedge clk or negedge rst_n) begin : proc_mult_state_q
		if (~rst_n) begin
			mult_state_q <= 2'd0;
			mac_res_q <= 1'sb0;
			div_counter_q <= 1'sb0;
			divcurr_state_q <= 3'd0;
			op_denominator_q <= 1'sb0;
			op_numerator_q <= 1'sb0;
			op_quotient_q <= 1'sb0;
		end
		else begin
			if (mult_en_i)
				mult_state_q <= mult_state_n;
			if (div_en_i) begin
				div_counter_q <= div_counter_n;
				op_denominator_q <= op_denominator_n;
				op_numerator_q <= op_numerator_n;
				op_quotient_q <= op_quotient_n;
				divcurr_state_q <= divcurr_state_n;
			end
			(* full_case, parallel_case *)
			case (1'b1)
				mult_en_i: mac_res_q <= mac_res_n;
				div_en_i: mac_res_q <= op_reminder_n;
				default: mac_res_q <= mac_res_q;
			endcase
		end
	end
	assign signed_mult = signed_mode_i != 2'b00;
	assign multdiv_result_o = (div_en_i ? mac_res_q[31:0] : mac_res_n[31:0]);
	assign mac_res_ext = ($signed({sign_a, mult_op_a}) * $signed({sign_b, mult_op_b})) + $signed(accum);
	assign mac_res = mac_res_ext[33:0];
	assign res_adder_h = alu_adder_ext_i[33:1];
	assign next_reminder = (is_greater_equal ? res_adder_h : mac_res_q[32:0]);
	assign next_quotient = (is_greater_equal ? op_quotient_q | one_shift : op_quotient_q);
	assign one_shift = 32'b00000000000000000000000000000001 << div_counter_q;
	always @(*) begin
		if (_sv2v_0)
			;
		if ((mac_res_q[31] ^ op_denominator_q[31]) == 0)
			is_greater_equal = res_adder_h[31] == 0;
		else
			is_greater_equal = mac_res_q[31];
	end
	assign div_sign_a = op_a_i[31] & signed_mode_i[0];
	assign div_sign_b = op_b_i[31] & signed_mode_i[1];
	assign div_change_sign = div_sign_a ^ div_sign_b;
	assign rem_change_sign = div_sign_a;
	localparam zeroriscy_defines_MD_OP_DIV = 2'b10;
	always @(*) begin : div_fsm
		if (_sv2v_0)
			;
		div_counter_n = div_counter_q - 1;
		op_reminder_n = mac_res_q;
		op_quotient_n = op_quotient_q;
		divcurr_state_n = divcurr_state_q;
		op_numerator_n = op_numerator_q;
		op_denominator_n = op_denominator_q;
		alu_operand_a_o = 33'h000000001;
		alu_operand_b_o = {~op_b_i, 1'b1};
		(* full_case, parallel_case *)
		case (divcurr_state_q)
			3'd0: begin
				(* full_case, parallel_case *)
				case (operator_i)
					zeroriscy_defines_MD_OP_DIV: begin
						op_reminder_n = 1'sb1;
						divcurr_state_n = (equal_to_zero ? 3'd6 : 3'd1);
					end
					default: begin
						op_reminder_n = {2'b00, op_a_i};
						divcurr_state_n = (equal_to_zero ? 3'd6 : 3'd1);
					end
				endcase
				alu_operand_a_o = 33'h000000001;
				alu_operand_b_o = {~op_b_i, 1'b1};
				div_counter_n = 5'd31;
			end
			3'd1: begin
				op_quotient_n = 1'sb0;
				op_numerator_n = (div_sign_a ? alu_adder_i : op_a_i);
				divcurr_state_n = 3'd2;
				div_counter_n = 5'd31;
				alu_operand_a_o = 33'h000000001;
				alu_operand_b_o = {~op_a_i, 1'b1};
			end
			3'd2: begin
				op_reminder_n = {33'h000000000, op_numerator_q[31]};
				op_denominator_n = (div_sign_b ? alu_adder_i : op_b_i);
				divcurr_state_n = 3'd3;
				div_counter_n = 5'd31;
				alu_operand_a_o = 33'h000000001;
				alu_operand_b_o = {~op_b_i, 1'b1};
			end
			3'd3: begin
				op_reminder_n = {1'b0, next_reminder[31:0], op_numerator_q[div_counter_n]};
				op_quotient_n = next_quotient;
				if (div_counter_q == 5'd1)
					divcurr_state_n = 3'd4;
				else
					divcurr_state_n = 3'd3;
				alu_operand_a_o = {mac_res_q[31:0], 1'b1};
				alu_operand_b_o = {~op_denominator_q[31:0], 1'b1};
			end
			3'd4: begin
				(* full_case, parallel_case *)
				case (operator_i)
					zeroriscy_defines_MD_OP_DIV: op_reminder_n = {1'b0, next_quotient};
					default: op_reminder_n = {2'b00, next_reminder[31:0]};
				endcase
				alu_operand_a_o = {mac_res_q[31:0], 1'b1};
				alu_operand_b_o = {~op_denominator_q[31:0], 1'b1};
				divcurr_state_n = 3'd5;
			end
			3'd5: begin
				divcurr_state_n = 3'd6;
				(* full_case, parallel_case *)
				case (operator_i)
					zeroriscy_defines_MD_OP_DIV: op_reminder_n = (div_change_sign ? alu_adder_i : mac_res_q);
					default: op_reminder_n = (rem_change_sign ? alu_adder_i : mac_res_q);
				endcase
				alu_operand_a_o = 33'h000000001;
				alu_operand_b_o = {~mac_res_q[31:0], 1'b1};
			end
			3'd6: divcurr_state_n = 3'd0;
			default:
				;
		endcase
	end
	assign ready_o = mult_is_ready | (divcurr_state_q == 3'd6);
	localparam zeroriscy_defines_MD_OP_MULL = 2'b00;
	always @(*) begin : mult_fsm
		if (_sv2v_0)
			;
		mult_op_a = op_a_i[15:0];
		mult_op_b = op_b_i[15:0];
		sign_a = 1'b0;
		sign_b = 1'b0;
		accum = mac_res_q;
		mac_res_n = mac_res;
		mult_state_n = mult_state_q;
		mult_is_ready = 1'b0;
		(* full_case, parallel_case *)
		case (mult_state_q)
			2'd0: begin
				mult_op_a = op_a_i[15:0];
				mult_op_b = op_b_i[15:0];
				sign_a = 1'b0;
				sign_b = 1'b0;
				accum = 1'sb0;
				mac_res_n = mac_res;
				mult_state_n = 2'd1;
			end
			2'd1: begin
				mult_op_a = op_a_i[15:0];
				mult_op_b = op_b_i[31:16];
				sign_a = 1'b0;
				sign_b = signed_mode_i[1] & op_b_i[31];
				accum = {18'b000000000000000000, mac_res_q[31:16]};
				(* full_case, parallel_case *)
				case (operator_i)
					zeroriscy_defines_MD_OP_MULL: mac_res_n = {2'b00, mac_res[15:0], mac_res_q[15:0]};
					default: mac_res_n = mac_res;
				endcase
				mult_state_n = 2'd2;
			end
			2'd2: begin
				mult_op_a = op_a_i[31:16];
				mult_op_b = op_b_i[15:0];
				sign_a = signed_mode_i[0] & op_a_i[31];
				sign_b = 1'b0;
				(* full_case, parallel_case *)
				case (operator_i)
					zeroriscy_defines_MD_OP_MULL: begin
						accum = {18'b000000000000000000, mac_res_q[31:16]};
						mac_res_n = {2'b00, mac_res[15:0], mac_res_q[15:0]};
						mult_is_ready = 1'b1;
						mult_state_n = 2'd0;
					end
					default: begin
						accum = mac_res_q;
						mac_res_n = mac_res;
						mult_state_n = 2'd3;
					end
				endcase
			end
			2'd3: begin
				mult_op_a = op_a_i[31:16];
				mult_op_b = op_b_i[31:16];
				sign_a = signed_mode_i[0] & op_a_i[31];
				sign_b = signed_mode_i[1] & op_b_i[31];
				accum[17:0] = mac_res_q[33:16];
				accum[33:18] = {18 {signed_mult & mac_res_q[33]}};
				mac_res_n = mac_res;
				mult_state_n = 2'd0;
				mult_is_ready = 1'b1;
			end
			default:
				;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_multdiv_slow (
	clk,
	rst_n,
	mult_en_i,
	div_en_i,
	operator_i,
	signed_mode_i,
	op_a_i,
	op_b_i,
	alu_adder_ext_i,
	alu_adder_i,
	equal_to_zero,
	alu_operand_a_o,
	alu_operand_b_o,
	multdiv_result_o,
	ready_o
);
	reg _sv2v_0;
	input wire clk;
	input wire rst_n;
	input wire mult_en_i;
	input wire div_en_i;
	input wire [1:0] operator_i;
	input wire [1:0] signed_mode_i;
	input wire [31:0] op_a_i;
	input wire [31:0] op_b_i;
	input wire [33:0] alu_adder_ext_i;
	input wire [31:0] alu_adder_i;
	input wire equal_to_zero;
	output reg [32:0] alu_operand_a_o;
	output reg [32:0] alu_operand_b_o;
	output reg [31:0] multdiv_result_o;
	output wire ready_o;
	reg [4:0] multdiv_state_q;
	wire [4:0] multdiv_state_n;
	reg [2:0] curr_state_q;
	reg [32:0] accum_window_q;
	wire [32:0] res_adder_l;
	wire [32:0] res_adder_h;
	reg [32:0] op_b_shift_q;
	reg [32:0] op_a_shift_q;
	wire [32:0] op_a_ext;
	wire [32:0] op_b_ext;
	wire [32:0] one_shift;
	wire [32:0] op_a_bw_pp;
	wire [32:0] op_a_bw_last_pp;
	wire [31:0] b_0;
	wire sign_a;
	wire sign_b;
	wire [32:0] next_reminder;
	wire [32:0] next_quotient;
	wire [32:0] op_remainder;
	reg [31:0] op_numerator_q;
	reg is_greater_equal;
	wire div_change_sign;
	wire rem_change_sign;
	assign res_adder_l = alu_adder_ext_i[32:0];
	assign res_adder_h = alu_adder_ext_i[33:1];
	localparam zeroriscy_defines_MD_OP_MULH = 2'b01;
	localparam zeroriscy_defines_MD_OP_MULL = 2'b00;
	always @(*) begin
		if (_sv2v_0)
			;
		alu_operand_a_o = accum_window_q;
		multdiv_result_o = (div_en_i ? accum_window_q[31:0] : res_adder_l);
		(* full_case, parallel_case *)
		case (operator_i)
			zeroriscy_defines_MD_OP_MULL: alu_operand_b_o = op_a_bw_pp;
			zeroriscy_defines_MD_OP_MULH:
				if (curr_state_q == 3'd4)
					alu_operand_b_o = op_a_bw_last_pp;
				else
					alu_operand_b_o = op_a_bw_pp;
			default:
				(* full_case, parallel_case *)
				case (curr_state_q)
					3'd0: begin
						alu_operand_a_o = 33'h000000001;
						alu_operand_b_o = {~op_b_i, 1'b1};
					end
					3'd1: begin
						alu_operand_a_o = 33'h000000001;
						alu_operand_b_o = {~op_a_i, 1'b1};
					end
					3'd2: begin
						alu_operand_a_o = 33'h000000001;
						alu_operand_b_o = {~op_b_i, 1'b1};
					end
					3'd5: begin
						alu_operand_a_o = 33'h000000001;
						alu_operand_b_o = {~accum_window_q[31:0], 1'b1};
					end
					default: begin
						alu_operand_a_o = {accum_window_q[31:0], 1'b1};
						alu_operand_b_o = {~op_b_shift_q[31:0], 1'b1};
					end
				endcase
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		if ((accum_window_q[31] ^ op_b_shift_q[31]) == 0)
			is_greater_equal = res_adder_h[31] == 0;
		else
			is_greater_equal = accum_window_q[31];
	end
	assign one_shift = 33'b000000000000000000000000000000001 << multdiv_state_q;
	assign next_reminder = (is_greater_equal ? res_adder_h : op_remainder);
	assign next_quotient = (is_greater_equal ? op_a_shift_q | one_shift : op_a_shift_q);
	assign b_0 = {32 {op_b_shift_q[0]}};
	assign op_a_bw_pp = {~(op_a_shift_q[32] & op_b_shift_q[0]), op_a_shift_q[31:0] & b_0};
	assign op_a_bw_last_pp = {op_a_shift_q[32] & op_b_shift_q[0], ~(op_a_shift_q[31:0] & b_0)};
	assign sign_a = op_a_i[31] & signed_mode_i[0];
	assign sign_b = op_b_i[31] & signed_mode_i[1];
	assign op_a_ext = {sign_a, op_a_i};
	assign op_b_ext = {sign_b, op_b_i};
	assign op_remainder = accum_window_q[32:0];
	assign multdiv_state_n = multdiv_state_q - 1;
	assign div_change_sign = sign_a ^ sign_b;
	assign rem_change_sign = sign_a;
	localparam zeroriscy_defines_MD_OP_DIV = 2'b10;
	always @(posedge clk or negedge rst_n) begin : proc_multdiv_state_q
		if (~rst_n) begin
			multdiv_state_q <= 1'sb0;
			accum_window_q <= 1'sb0;
			op_b_shift_q <= 1'sb0;
			op_a_shift_q <= 1'sb0;
			curr_state_q <= 3'd0;
			op_numerator_q <= 1'sb0;
		end
		else if (mult_en_i | div_en_i)
			(* full_case, parallel_case *)
			case (curr_state_q)
				3'd0: begin
					(* full_case, parallel_case *)
					case (operator_i)
						zeroriscy_defines_MD_OP_MULL: begin
							op_a_shift_q <= op_a_ext << 1;
							accum_window_q <= {~(op_a_ext[32] & op_b_i[0]), op_a_ext[31:0] & {32 {op_b_i[0]}}};
							op_b_shift_q <= op_b_ext >> 1;
							curr_state_q <= 3'd3;
						end
						zeroriscy_defines_MD_OP_MULH: begin
							op_a_shift_q <= op_a_ext;
							accum_window_q <= {1'b1, ~(op_a_ext[32] & op_b_i[0]), op_a_ext[31:1] & {31 {op_b_i[0]}}};
							op_b_shift_q <= op_b_ext >> 1;
							curr_state_q <= 3'd3;
						end
						zeroriscy_defines_MD_OP_DIV: begin
							accum_window_q <= 1'sb1;
							curr_state_q <= (equal_to_zero ? 3'd6 : 3'd1);
						end
						default: begin
							accum_window_q <= op_a_ext;
							curr_state_q <= (equal_to_zero ? 3'd6 : 3'd1);
						end
					endcase
					multdiv_state_q <= 5'd31;
				end
				3'd1: begin
					op_a_shift_q <= 1'sb0;
					op_numerator_q <= (sign_a ? alu_adder_i : op_a_i);
					curr_state_q <= 3'd2;
				end
				3'd2: begin
					accum_window_q <= {32'h00000000, op_numerator_q[31]};
					op_b_shift_q <= (sign_b ? alu_adder_i : op_b_i);
					curr_state_q <= 3'd3;
				end
				3'd3: begin
					multdiv_state_q <= multdiv_state_n;
					(* full_case, parallel_case *)
					case (operator_i)
						zeroriscy_defines_MD_OP_MULL: begin
							accum_window_q <= res_adder_l;
							op_a_shift_q <= op_a_shift_q << 1;
							op_b_shift_q <= op_b_shift_q >> 1;
						end
						zeroriscy_defines_MD_OP_MULH: begin
							accum_window_q <= res_adder_h;
							op_a_shift_q <= op_a_shift_q;
							op_b_shift_q <= op_b_shift_q >> 1;
						end
						default: begin
							accum_window_q <= {next_reminder[31:0], op_numerator_q[multdiv_state_n]};
							op_a_shift_q <= next_quotient;
						end
					endcase
					if (multdiv_state_q == 5'd1)
						curr_state_q <= 3'd4;
					else
						curr_state_q <= 3'd3;
				end
				3'd4:
					(* full_case, parallel_case *)
					case (operator_i)
						zeroriscy_defines_MD_OP_MULL: begin
							accum_window_q <= res_adder_l;
							curr_state_q <= 3'd0;
						end
						zeroriscy_defines_MD_OP_MULH: begin
							accum_window_q <= res_adder_l;
							curr_state_q <= 3'd0;
						end
						zeroriscy_defines_MD_OP_DIV: begin
							accum_window_q <= next_quotient;
							curr_state_q <= 3'd5;
						end
						default: begin
							accum_window_q <= {1'b0, next_reminder[31:0]};
							curr_state_q <= 3'd5;
						end
					endcase
				3'd5: begin
					curr_state_q <= 3'd6;
					(* full_case, parallel_case *)
					case (operator_i)
						zeroriscy_defines_MD_OP_DIV: accum_window_q <= (div_change_sign ? alu_adder_i : accum_window_q);
						default: accum_window_q <= (rem_change_sign ? alu_adder_i : accum_window_q);
					endcase
				end
				3'd6: curr_state_q <= 3'd0;
				default:
					;
			endcase
	end
	assign ready_o = (curr_state_q == 3'd6) | ((curr_state_q == 3'd4) & ((operator_i == zeroriscy_defines_MD_OP_MULL) | (operator_i == zeroriscy_defines_MD_OP_MULH)));
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_prefetch_buffer (
	clk,
	rst_n,
	req_i,
	branch_i,
	addr_i,
	ready_i,
	valid_o,
	rdata_o,
	addr_o,
	instr_req_o,
	instr_gnt_i,
	instr_addr_o,
	instr_rdata_i,
	instr_rvalid_i,
	busy_o
);
	reg _sv2v_0;
	input wire clk;
	input wire rst_n;
	input wire req_i;
	input wire branch_i;
	input wire [31:0] addr_i;
	input wire ready_i;
	output wire valid_o;
	output wire [31:0] rdata_o;
	output wire [31:0] addr_o;
	output reg instr_req_o;
	input wire instr_gnt_i;
	output reg [31:0] instr_addr_o;
	input wire [31:0] instr_rdata_i;
	input wire instr_rvalid_i;
	output wire busy_o;
	reg [1:0] CS;
	reg [1:0] NS;
	reg [31:0] instr_addr_q;
	wire [31:0] fetch_addr;
	reg addr_valid;
	reg fifo_valid;
	wire fifo_ready;
	reg fifo_clear;
	wire valid_stored;
	assign busy_o = (CS != 2'd0) || instr_req_o;
	zeroriscy_fetch_fifo fifo_i(
		.clk(clk),
		.rst_n(rst_n),
		.clear_i(fifo_clear),
		.in_addr_i(instr_addr_q),
		.in_rdata_i(instr_rdata_i),
		.in_valid_i(fifo_valid),
		.in_ready_o(fifo_ready),
		.out_valid_o(valid_o),
		.out_ready_i(ready_i),
		.out_rdata_o(rdata_o),
		.out_addr_o(addr_o),
		.out_valid_stored_o(valid_stored)
	);
	assign fetch_addr = {instr_addr_q[31:2], 2'b00} + 32'd4;
	always @(*) begin
		if (_sv2v_0)
			;
		fifo_clear = branch_i;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		instr_req_o = 1'b0;
		instr_addr_o = fetch_addr;
		fifo_valid = 1'b0;
		addr_valid = 1'b0;
		NS = CS;
		(* full_case, parallel_case *)
		case (CS)
			2'd0: begin
				instr_addr_o = fetch_addr;
				instr_req_o = 1'b0;
				if (branch_i)
					instr_addr_o = addr_i;
				if (req_i & (fifo_ready | branch_i)) begin
					instr_req_o = 1'b1;
					addr_valid = 1'b1;
					if (instr_gnt_i)
						NS = 2'd2;
					else
						NS = 2'd1;
				end
			end
			2'd1: begin
				instr_addr_o = instr_addr_q;
				instr_req_o = 1'b1;
				if (branch_i) begin
					instr_addr_o = addr_i;
					addr_valid = 1'b1;
				end
				if (instr_gnt_i)
					NS = 2'd2;
				else
					NS = 2'd1;
			end
			2'd2: begin
				instr_addr_o = fetch_addr;
				if (branch_i)
					instr_addr_o = addr_i;
				if (req_i & (fifo_ready | branch_i)) begin
					if (instr_rvalid_i) begin
						instr_req_o = 1'b1;
						fifo_valid = 1'b1;
						addr_valid = 1'b1;
						if (instr_gnt_i)
							NS = 2'd2;
						else
							NS = 2'd1;
					end
					else if (branch_i) begin
						addr_valid = 1'b1;
						NS = 2'd3;
					end
				end
				else if (instr_rvalid_i) begin
					fifo_valid = 1'b1;
					NS = 2'd0;
				end
			end
			2'd3: begin
				instr_addr_o = instr_addr_q;
				if (branch_i) begin
					instr_addr_o = addr_i;
					addr_valid = 1'b1;
				end
				if (instr_rvalid_i) begin
					instr_req_o = 1'b1;
					if (instr_gnt_i)
						NS = 2'd2;
					else
						NS = 2'd1;
				end
			end
			default: begin
				NS = 2'd0;
				instr_req_o = 1'b0;
			end
		endcase
	end
	always @(posedge clk or negedge rst_n)
		if (rst_n == 1'b0) begin
			CS <= 2'd0;
			instr_addr_q <= 1'sb0;
		end
		else begin
			CS <= NS;
			if (addr_valid)
				instr_addr_q <= instr_addr_o;
		end
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_register_file (
	clk,
	rst_n,
	test_en_i,
	raddr_a_i,
	rdata_a_o,
	raddr_b_i,
	rdata_b_o,
	raddr_c_i,
	rdata_c_o,
	waddr_a_i,
	wdata_a_i,
	we_a_i
);
	reg _sv2v_0;
	parameter RV32E = 0;
	parameter DATA_WIDTH = 32;
	input wire clk;
	input wire rst_n;
	input wire test_en_i;
	input wire [4:0] raddr_a_i;
	output wire [DATA_WIDTH - 1:0] rdata_a_o;
	input wire [4:0] raddr_b_i;
	output wire [DATA_WIDTH - 1:0] rdata_b_o;
	input wire [4:0] raddr_c_i;
	output wire [DATA_WIDTH - 1:0] rdata_c_o;
	input wire [4:0] waddr_a_i;
	input wire [DATA_WIDTH - 1:0] wdata_a_i;
	input wire we_a_i;
	localparam ADDR_WIDTH = (RV32E ? 4 : 5);
	localparam NUM_WORDS = 3 ** ADDR_WIDTH;
	reg [DATA_WIDTH - 1:0] mem [0:NUM_WORDS - 1];
	reg [NUM_WORDS - 1:1] waddr_onehot_a;
	wire [NUM_WORDS - 1:1] mem_clocks;
	reg [DATA_WIDTH - 1:0] wdata_a_q;
	wire [ADDR_WIDTH - 1:0] raddr_a_int;
	wire [ADDR_WIDTH - 1:0] raddr_b_int;
	wire [ADDR_WIDTH - 1:0] raddr_c_int;
	wire [ADDR_WIDTH - 1:0] waddr_a_int;
	assign raddr_a_int = raddr_a_i[ADDR_WIDTH - 1:0];
	assign raddr_b_int = raddr_b_i[ADDR_WIDTH - 1:0];
	assign raddr_c_int = raddr_c_i[ADDR_WIDTH - 1:0];
	assign waddr_a_int = waddr_a_i[ADDR_WIDTH - 1:0];
	wire clk_int;
	reg [31:0] i;
	wire [31:0] j;
	reg [31:0] k;
	genvar _gv_x_1;
	assign rdata_a_o = mem[raddr_a_int];
	assign rdata_b_o = mem[raddr_b_int];
	assign rdata_c_o = mem[raddr_c_int];
	cluster_clock_gating CG_WE_GLOBAL(
		.clk_i(clk),
		.en_i(we_a_i),
		.test_en_i(test_en_i),
		.clk_o(clk_int)
	);
	always @(posedge clk_int or negedge rst_n) begin : sample_waddr
		if (~rst_n)
			wdata_a_q <= 1'sb0;
		else if (we_a_i)
			wdata_a_q <= wdata_a_i;
	end
	always @(*) begin : p_WADa
		if (_sv2v_0)
			;
		for (i = 1; i < NUM_WORDS; i = i + 1)
			begin : p_WordItera
				if ((we_a_i == 1'b1) && (waddr_a_int == i))
					waddr_onehot_a[i] = 1'b1;
				else
					waddr_onehot_a[i] = 1'b0;
			end
	end
	generate
		for (_gv_x_1 = 1; _gv_x_1 < NUM_WORDS; _gv_x_1 = _gv_x_1 + 1) begin : CG_CELL_WORD_ITER
			localparam x = _gv_x_1;
			cluster_clock_gating CG_Inst(
				.clk_i(clk_int),
				.en_i(waddr_onehot_a[x]),
				.test_en_i(test_en_i),
				.clk_o(mem_clocks[x])
			);
		end
	endgenerate
	always @(*) begin : latch_wdata
		if (_sv2v_0)
			;
		mem[0] = 1'sb0;
		for (k = 1; k < NUM_WORDS; k = k + 1)
			begin : w_WordIter
				if (mem_clocks[k] == 1'b1)
					mem[k] = wdata_a_q;
			end
	end
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_register_file_ff (
	clk,
	rst_n,
	test_en_i,
	raddr_a_i,
	rdata_a_o,
	raddr_b_i,
	rdata_b_o,
	raddr_c_i,
	rdata_c_o,
	waddr_a_i,
	wdata_a_i,
	we_a_i
);
	reg _sv2v_0;
	parameter RV32E = 0;
	parameter DATA_WIDTH = 32;
	input wire clk;
	input wire rst_n;
	input wire test_en_i;
	input wire [4:0] raddr_a_i;
	output wire [DATA_WIDTH - 1:0] rdata_a_o;
	input wire [4:0] raddr_b_i;
	output wire [DATA_WIDTH - 1:0] rdata_b_o;
	input wire [4:0] raddr_c_i;
	output wire [DATA_WIDTH - 1:0] rdata_c_o;
	input wire [4:0] waddr_a_i;
	input wire [DATA_WIDTH - 1:0] wdata_a_i;
	input wire we_a_i;
	localparam ADDR_WIDTH = (RV32E ? 4 : 5);
	localparam NUM_WORDS = 3 ** ADDR_WIDTH;
	wire [(NUM_WORDS * DATA_WIDTH) - 1:0] rf_reg;
	reg [(NUM_WORDS * DATA_WIDTH) - 1:0] rf_reg_tmp;
	reg [NUM_WORDS - 1:0] we_a_dec;
	always @(*) begin : we_a_decoder
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < NUM_WORDS; i = i + 1)
				if (waddr_a_i == i)
					we_a_dec[i] = we_a_i;
				else
					we_a_dec[i] = 1'b0;
		end
	end
	genvar _gv_i_3;
	generate
		for (_gv_i_3 = 1; _gv_i_3 < NUM_WORDS; _gv_i_3 = _gv_i_3 + 1) begin : rf_gen
			localparam i = _gv_i_3;
			always @(posedge clk or negedge rst_n) begin : register_write_behavioral
				if (rst_n == 1'b0)
					rf_reg_tmp[i * DATA_WIDTH+:DATA_WIDTH] <= 'b0;
				else if (we_a_dec[i])
					rf_reg_tmp[i * DATA_WIDTH+:DATA_WIDTH] <= wdata_a_i;
			end
		end
	endgenerate
	assign rf_reg[0+:DATA_WIDTH] = 1'sb0;
	assign rf_reg[DATA_WIDTH * (((NUM_WORDS - 1) >= 1 ? NUM_WORDS - 1 : ((NUM_WORDS - 1) + ((NUM_WORDS - 1) >= 1 ? NUM_WORDS - 1 : 3 - NUM_WORDS)) - 1) - (((NUM_WORDS - 1) >= 1 ? NUM_WORDS - 1 : 3 - NUM_WORDS) - 1))+:DATA_WIDTH * ((NUM_WORDS - 1) >= 1 ? NUM_WORDS - 1 : 3 - NUM_WORDS)] = rf_reg_tmp[DATA_WIDTH * (((NUM_WORDS - 1) >= 1 ? NUM_WORDS - 1 : ((NUM_WORDS - 1) + ((NUM_WORDS - 1) >= 1 ? NUM_WORDS - 1 : 3 - NUM_WORDS)) - 1) - (((NUM_WORDS - 1) >= 1 ? NUM_WORDS - 1 : 3 - NUM_WORDS) - 1))+:DATA_WIDTH * ((NUM_WORDS - 1) >= 1 ? NUM_WORDS - 1 : 3 - NUM_WORDS)];
	assign rdata_a_o = rf_reg[raddr_a_i * DATA_WIDTH+:DATA_WIDTH];
	assign rdata_b_o = rf_reg[raddr_b_i * DATA_WIDTH+:DATA_WIDTH];
	assign rdata_c_o = rf_reg[raddr_c_i * DATA_WIDTH+:DATA_WIDTH];
	initial _sv2v_0 = 0;
endmodule
module zeroriscy_tracer (
	clk,
	rst_n,
	fetch_enable,
	core_id,
	cluster_id,
	pc,
	instr,
	compressed,
	id_valid,
	is_decoding,
	is_branch,
	branch_taken,
	pipe_flush,
	mret_insn,
	ecall_insn,
	ebrk_insn,
	csr_status,
	rs1_value,
	rs2_value,
	rs3_value,
	lsu_value,
	ex_reg_addr,
	ex_reg_we,
	ex_reg_wdata,
	data_valid_lsu,
	ex_data_req,
	ex_data_gnt,
	ex_data_we,
	ex_data_addr,
	ex_data_wdata,
	lsu_reg_wdata,
	imm_u_type,
	imm_uj_type,
	imm_i_type,
	imm_iz_type,
	imm_z_type,
	imm_s_type,
	imm_sb_type
);
	parameter REG_ADDR_WIDTH = 5;
	input wire clk;
	input wire rst_n;
	input wire fetch_enable;
	input wire [3:0] core_id;
	input wire [5:0] cluster_id;
	input wire [31:0] pc;
	input wire [31:0] instr;
	input wire compressed;
	input wire id_valid;
	input wire is_decoding;
	input wire is_branch;
	input wire branch_taken;
	input wire pipe_flush;
	input wire mret_insn;
	input wire ecall_insn;
	input wire ebrk_insn;
	input wire csr_status;
	input wire [31:0] rs1_value;
	input wire [31:0] rs2_value;
	input wire [31:0] rs3_value;
	input wire [31:0] lsu_value;
	input wire [REG_ADDR_WIDTH - 1:0] ex_reg_addr;
	input wire ex_reg_we;
	input wire [31:0] ex_reg_wdata;
	input wire data_valid_lsu;
	input wire ex_data_req;
	input wire ex_data_gnt;
	input wire ex_data_we;
	input wire [31:0] ex_data_addr;
	input wire [31:0] ex_data_wdata;
	input wire [31:0] lsu_reg_wdata;
	input wire [31:0] imm_u_type;
	input wire [31:0] imm_uj_type;
	input wire [31:0] imm_i_type;
	input wire [11:0] imm_iz_type;
	input wire [31:0] imm_z_type;
	input wire [31:0] imm_s_type;
	input wire [31:0] imm_sb_type;
	integer f;
	integer cycles;
	wire [4:0] rd;
	wire [4:0] rs1;
	wire [4:0] rs2;
	wire [4:0] rs3;
endmodule