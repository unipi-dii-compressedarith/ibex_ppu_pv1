// Compiled by morty-0.8.0 / 2023-04-12 10:24:16.166300949 +02:00


package ppu_pkg;

parameter N = 16;
parameter ES = 1;
localparam OP_BITS = $clog2(5);
typedef enum logic [OP_BITS-1:0] {
  ADD, SUB,
  MUL, DIV,
  FMADD,
  F2P, P2F
} operation_e;


typedef struct packed {
  logic [N-1:0] bits;
} posit_t;

typedef struct packed {
  posit_t posit;
  logic   special_tag;
} posit_special_t;


parameter S = $clog2(N);

parameter TE_BITS = (ES + 1) + (S + 1);

parameter REG_LEN_BITS = S + 1;

parameter MANT_LEN_BITS = S + 1;

parameter K_BITS = S + 2; 
parameter FRAC_SIZE = N - 1;

parameter MANT_SIZE = N - 2;

typedef logic [TE_BITS-1:0] exponent_t;

typedef struct packed {
  logic                 sign;
  exponent_t            total_exponent;
  logic [MANT_SIZE-1:0] mant;
} fir_t;


parameter MS = MANT_SIZE;  
parameter MAX_TE_DIFF = MS;  parameter MTD = MAX_TE_DIFF;  

parameter RECIPROCATE_MANT_SIZE = 2 * MANT_SIZE;
parameter RMS = RECIPROCATE_MANT_SIZE;  

parameter MANT_MUL_RESULT_SIZE = 2 * MS;
parameter MANT_ADD_RESULT_SIZE = MS + MTD + 1;
parameter MANT_SUB_RESULT_SIZE = MS + MTD;
parameter MANT_DIV_RESULT_SIZE = MS + RMS;

parameter FRAC_FULL_SIZE = MANT_DIV_RESULT_SIZE - 2; 
typedef struct packed {
  logic                       sign;
  exponent_t                  total_exponent;
  logic [FRAC_FULL_SIZE-1:0]  frac;
} long_fir_t; 
typedef struct packed {
  long_fir_t  long_fir;
  logic       frac_truncated;
} ops_out_meta_t;



parameter ZERO = {16{1'b0}};
parameter NAR = {1'b1, {16 - 1{1'b0}}};



`define STRINGIFY(DEFINE) $sformatf("%0s", `"DEFINE`")













parameter fx_1_466___N4 = 2'd3; parameter fx_1_466___N5 = 3'd6; parameter fx_1_466___N6 = 4'd12; parameter fx_1_466___N7 = 5'd23; parameter fx_1_466___N8 = 6'd47; parameter fx_1_466___N9 = 7'd93; parameter fx_1_466___N10 = 8'd186; parameter fx_1_466___N11 = 9'd373; parameter fx_1_466___N12 = 10'd746; parameter fx_1_466___N13 = 11'd1492; parameter fx_1_466___N14 = 12'd2983; parameter fx_1_466___N15 = 13'd5967; parameter fx_1_466___N16 = 14'd11934; parameter fx_1_466___N17 = 15'd23868; parameter fx_1_466___N18 = 16'd47736; parameter fx_1_466___N19 = 17'd95472; parameter fx_1_466___N20 = 18'd190944; parameter fx_1_466___N21 = 19'd381887; parameter fx_1_466___N22 = 20'd763775; parameter fx_1_466___N23 = 21'd1527549; parameter fx_1_466___N24 = 22'd3055098; parameter fx_1_466___N25 = 23'd6110197; parameter fx_1_466___N26 = 24'd12220393; parameter fx_1_466___N27 = 25'd24440787; parameter fx_1_466___N28 = 26'd48881573; parameter fx_1_466___N29 = 27'd97763147; parameter fx_1_466___N30 = 28'd195526294; parameter fx_1_466___N31 = 29'd391052588; parameter fx_1_466___N32 = 30'd782105176; 
parameter fx_1_0012___N4 = 3'd4; parameter fx_1_0012___N5 = 5'd16; parameter fx_1_0012___N6 = 7'd64; parameter fx_1_0012___N7 = 9'd256; parameter fx_1_0012___N8 = 11'd1025; parameter fx_1_0012___N9 = 13'd4100; parameter fx_1_0012___N10 = 15'd16399; parameter fx_1_0012___N11 = 17'd65597; parameter fx_1_0012___N12 = 19'd262388; parameter fx_1_0012___N13 = 21'd1049550; parameter fx_1_0012___N14 = 23'd4198201; parameter fx_1_0012___N15 = 25'd16792802; parameter fx_1_0012___N16 = 27'd67171208; parameter fx_1_0012___N17 = 29'd268684833; parameter fx_1_0012___N18 = 31'd1074739333; parameter fx_1_0012___N19 = 33'd4298957332; parameter fx_1_0012___N20 = 35'd17195829328; parameter fx_1_0012___N21 = 37'd68783317313; parameter fx_1_0012___N22 = 39'd275133269251; parameter fx_1_0012___N23 = 41'd1100533077005; parameter fx_1_0012___N24 = 43'd4402132308019; parameter fx_1_0012___N25 = 45'd17608529232075; parameter fx_1_0012___N26 = 47'd70434116928301; parameter fx_1_0012___N27 = 49'd281736467713206; parameter fx_1_0012___N28 = 51'd1126945870852824; parameter fx_1_0012___N29 = 53'd4507783483411295; parameter fx_1_0012___N30 = 55'd18031133933645177; parameter fx_1_0012___N31 = 57'd72124535734580705; parameter fx_1_0012___N32 = 59'd288498142938322817; 
parameter fx_2___N4 = 4'd8; parameter fx_2___N5 = 6'd32; parameter fx_2___N6 = 8'd128; parameter fx_2___N7 = 10'd512; parameter fx_2___N8 = 12'd2048; parameter fx_2___N9 = 14'd8192; parameter fx_2___N10 = 16'd32768; parameter fx_2___N11 = 18'd131072; parameter fx_2___N12 = 20'd524288; parameter fx_2___N13 = 22'd2097152; parameter fx_2___N14 = 24'd8388608; parameter fx_2___N15 = 26'd33554432; parameter fx_2___N16 = 28'd134217728; parameter fx_2___N17 = 30'd536870912; parameter fx_2___N18 = 32'd2147483648; parameter fx_2___N19 = 34'd8589934592; parameter fx_2___N20 = 36'd34359738368; parameter fx_2___N21 = 38'd137438953472; parameter fx_2___N22 = 40'd549755813888; parameter fx_2___N23 = 42'd2199023255552; parameter fx_2___N24 = 44'd8796093022208; parameter fx_2___N25 = 46'd35184372088832; parameter fx_2___N26 = 48'd140737488355328; parameter fx_2___N27 = 50'd562949953421312; parameter fx_2___N28 = 52'd2251799813685248; parameter fx_2___N29 = 54'd9007199254740992; parameter fx_2___N30 = 56'd36028797018963968; parameter fx_2___N31 = 58'd144115188075855872; parameter fx_2___N32 = 60'd576460752303423488; 






function [(N)-1:0] c2(input [(N)-1:0] a);
  c2 = ~a + 1'b1;
endfunction






function [N-1:0] abs(input [N-1:0] in);
  abs = in[N-1] == 0 ? in : c2(in);
endfunction

function [N-1:0] min(input [N-1:0] a, b);
  min = $signed(a) <= $signed(b) ? a : b;
endfunction

function [N-1:0] max(input [N-1:0] a, b);
  max = a >= b ? a : b;
endfunction

function is_negative(input [S:0] k);
  is_negative = k[S];
endfunction

function [N-1:0] shl(input [N-1:0] bits, input [N-1:0] rhs);
  shl = rhs[N-1] == 0 ? bits << rhs : bits >> c2(rhs);
endfunction



endpackage: ppu_pkg
module ppu_core_ops 
  import ppu_pkg::*;
#(
  parameter N = -1,
  parameter ES = -1
)(
  input                                         clk_i,
  input                                         rst_i,
  input   ppu_pkg::posit_t                      p1_i,
  input   ppu_pkg::posit_t                      p2_i,
  input   ppu_pkg::posit_t                      p3_i,
  input   ppu_pkg::operation_e                  op_i,
  output  ppu_pkg::operation_e                  op_o,   input                                         stall_i,
output  ppu_pkg::posit_t                      pout_o
);
    
  ppu_pkg::operation_e op_st0, op_st1;
  assign op_st0 = op_i; 

  wire [K_BITS-1:0] k1, k2;
wire [ES-1:0] exp1, exp2;
wire [MANT_SIZE-1:0] mant1, mant2;
  wire [(3*MANT_SIZE)-1:0] mant_out_ops;
  exponent_t te1, te2, te_out_ops;

  logic sign1, sign2;

  posit_t      p1_cond, p2_cond, p3_cond;
  logic        is_special_or_trivial;
  posit_t      pout_special_or_trivial;
  
  logic [(N+1)-1:0] p_special_st0, p_special_st1, p_special_st2, p_special_st3;
  input_conditioning #(
    .N          (N)
  ) input_conditioning (
    .p1_i       (p1_i),
    .p2_i       (p2_i),
    .p3_i       (p3_i),
    .op_i       (op_st0),
    .p1_o       (p1_cond),
    .p2_o       (p2_cond),
    .p3_o       (p3_cond),
    .p_special_o(p_special_st0)
  );

  assign is_special_or_trivial = p_special_st3[0];
  assign pout_special_or_trivial = p_special_st3 >> 1;

  ppu_pkg::fir_t fir1_st0, fir1_st1;
  ppu_pkg::fir_t fir2_st0, fir2_st1;
  ppu_pkg::fir_t fir3_st0, fir3_st1;

  assign fir1_st1 = fir1_st0;
  assign fir2_st1 = fir2_st0;
  assign fir3_st1 = fir3_st0;
  assign op_st1 = op_st0;

  posit_to_fir #(
    .N          (N),
    .ES         (ES)
  ) posit_to_fir1 (
    .p_cond_i   (p1_cond),
    .fir_o      (fir1_st0)
  );

  wire [N-1:0] posit_in_posit_to_fir2;
  assign posit_in_posit_to_fir2 =
p2_cond;

  posit_to_fir #(
    .N          (N),
    .ES         (ES)
  ) posit_to_fir2 (
    .p_cond_i   (posit_in_posit_to_fir2),
    .fir_o      (fir2_st0)
  );


  posit_to_fir #(
    .N          (N),
    .ES         (ES)
  ) posit_to_fir3 (
    .p_cond_i   (p3_cond),
    .fir_o      (fir3_st0)
  );

exponent_t ops_te_out;
  wire [FRAC_FULL_SIZE-1:0] ops_frac_full;


  wire sign_out_ops;
  wire [((1 + TE_BITS + FRAC_FULL_SIZE) + 1)-1:0] ops_result;
  ops #(
    .N              (N)
  ) ops_inst (
    .clk_i          (clk_i),
    .rst_i          (rst_i),
    .op_i           (op_st1),
    .fir1_i         (fir1_st1),
    .fir2_i         (fir2_st1),
    .fir3_i         (fir3_st1),
    .ops_result_o   (ops_result)
  );


  wire frac_truncated;

  wire [N-1:0] pout_non_special;


  logic [((1 + TE_BITS + FRAC_FULL_SIZE) + 1)-1:0] ops_wire_st0, ops_wire_st1;

  assign ops_wire_st0 =
ops_result;

  
  fir_to_posit #(
    .N                (N),
    .ES               (ES),
    .FIR_TOTAL_SIZE   (1 + TE_BITS + FRAC_FULL_SIZE)
  ) fir_to_posit_inst (
    .ops_result_i     (ops_wire_st1),
    .posit_o          (pout_non_special)
  );

  assign pout_o = is_special_or_trivial ? pout_special_or_trivial : pout_non_special;

assign ops_wire_st1 = ops_wire_st0;
  assign p_special_st1 = p_special_st0;   assign p_special_st2 = p_special_st1;
  assign p_special_st3 = p_special_st2;   assign op_o = op_st1;
endmodule: ppu_core_ops
module posit_to_fir 
  import ppu_pkg::*;
#(
  parameter N  = -1,
  parameter ES = -1
) (
  input posit_t p_cond_i,
  output fir_t fir_o
);

  posit_decoder #(
    .N        (N),
    .ES       (ES)
  ) posit_decoder_inst (
    .bits_i   (p_cond_i),
    .fir_o    (fir_o)
  );

endmodule: posit_to_fir
module fir_to_posit 
  import ppu_pkg::*;
#(
  parameter N = -1,
  parameter ES = -1,
  parameter FIR_TOTAL_SIZE = -1
) (
  input ops_out_meta_t  ops_result_i,
  output posit_t        posit_o
);

  long_fir_t fir;
  logic frac_truncated;    assign fir = ops_result_i.long_fir;
  assign frac_truncated = ops_result_i.frac_truncated;

  logic sign;
  exponent_t te;
  wire [FRAC_FULL_SIZE-1:0] frac_full;
  assign {sign, te, frac_full} = fir;


  wire [MANT_SIZE-1:0] frac;
  wire [K_BITS-1:0] k;
wire [ES-1:0] next_exp;
pack_fields #(
    .N                (N),
    .ES               (ES)
  ) pack_fields_inst (
    .frac_full_i      (frac_full),     .total_exp_i      (te),
    .frac_truncated_i (frac_truncated),

    .k_o              (k),
.next_exp_o       (next_exp),
.frac_o           (frac), 
    .round_bit        (round_bit),
    .sticky_bit       (sticky_bit),
    .k_is_oob         (k_is_oob),
    .non_zero_frac_field_size(non_zero_frac_field_size)
  );


  wire [N-1:0] posit_encoded;
  posit_encoder #(
    .N              (N),
    .ES             (ES)
) posit_encoder_inst (
    .is_zero_i      (),
    .is_nar_i       (),
    .sign           (1'b0),
    .k              (k),
.exp            (next_exp),
.frac           (frac),
    .posit          (posit_encoded)
  );


  wire [N-1:0] posit_pre_sign;

  round_posit #(
    .N              (N)
  ) round_posit_inst (
    .posit          (posit_encoded),
    .round_bit      (round_bit),
    .sticky_bit     (sticky_bit),
    .k_is_oob       (k_is_oob),
    .non_zero_frac_field_size(non_zero_frac_field_size),
    .posit_rounded  (posit_pre_sign)
  );


  set_sign #(
    .N              (N)
  ) set_sign_inst (
    .posit_in       (posit_pre_sign),
    .sign           (sign),
    .posit_out      (posit_o)
  );

endmodule: fir_to_posit
`define A // remove this
module input_conditioning 
  import ppu_pkg::*;
#(
  parameter N = -1
) (
  input  posit_t            p1_i,
  input  posit_t            p2_i,
  input  posit_t            p3_i,
  input  operation_e        op_i,
  output posit_t            p1_o,
  output posit_t            p2_o,
  output posit_t            p3_o,
  output posit_special_t    p_special_o );

  posit_t _p1, _p2;
  assign _p1 = p1_i;
  assign _p2 = (op_i == SUB) ? c2(p2_i) : p2_i;

  logic op_is_add_or_sub;
  assign op_is_add_or_sub = (op_i == ADD || op_i == SUB);

  assign {p1_o, p2_o} = (op_is_add_or_sub && abs(_p2) > abs(_p1)) ? {_p2, _p1} : {_p1, _p2};

  logic is_special_or_trivial;
  posit_t pout_special_or_trivial;


  handle_special_or_trivial #(
    .N      (N)
  ) handle_special_or_trivial_inst (
    .op_i   (op_i),
    .p1_i   (p1_i),
    .p2_i   (p2_i),
    .p3_i   (p3_i),
    .pout_o (pout_special_or_trivial)
  );

  assign is_special_or_trivial =
        op_i === F2P  
    ? 0 :
        p1_i == ZERO
    || p1_i == NAR
    || p2_i == ZERO
    || p2_i == NAR
    || (op_i == SUB && p1_i == p2_i)
    || (op_i == ADD && p1_i == c2(
        p2_i
    ));


  assign p_special_o.posit.bits = pout_special_or_trivial;
  assign p_special_o.special_tag = is_special_or_trivial;

endmodule: input_conditioning





module handle_special_or_trivial 
  import ppu_pkg::*;  
#(
  parameter N = -1
) (
  input   operation_e   op_i,
  input   posit_t       p1_i,
  input   posit_t       p2_i,
  input   posit_t       p3_i,
  output  posit_t       pout_o
);

  posit_t p_out_lut_mul, p_out_lut_add, p_out_lut_sub, p_out_lut_div;

  lut_mul #(
    .N          (N)
  ) lut_mul_inst (
    .p1         (p1_i),
    .p2         (p2_i),
    .p_out      (p_out_lut_mul)
  );

  lut_add #(
    .N          (N)
  ) lut_add_inst (
    .p1         (p1_i),
    .p2         (p2_i),
    .p_out      (p_out_lut_add)
  );

  lut_sub #(
    .N          (N)
  ) lut_sub_inst (
    .p1         (p1_i),
    .p2         (p2_i),
    .p_out      (p_out_lut_sub)
  );

  lut_div #(
    .N          (N)
  ) lut_div_inst (
    .p1         (p1_i),
    .p2         (p2_i),
    .p_out      (p_out_lut_div)
  );

  assign pout_o = op_i == MUL
    ? p_out_lut_mul : op_i == ADD
    ? p_out_lut_add : op_i == SUB
    ? p_out_lut_sub : 
      p_out_lut_div;

endmodule: handle_special_or_trivial


module lut_mul
  import ppu_pkg::*;
#(
  parameter N = -1
) (
  input   posit_t p1,
  input   posit_t p2,
  output  posit_t p_out
);

  wire [(2*N)-1:0] addr;
  assign addr = {p1, p2};

  always_comb begin
    case (p1)
      ZERO:    p_out = p2 == NAR || p2 == ZERO ? p2 : ZERO;
      NAR:     p_out = NAR;
      default: p_out = p2;
    endcase
  end
endmodule: lut_mul

module lut_add
  import ppu_pkg::*;
#(
  parameter N = -1
) (
  input   posit_t p1,
  input   posit_t p2,
  output  posit_t p_out
);

  always_comb begin
    case (p1)
      ZERO:    p_out = p2;
      NAR:     p_out = NAR;
      default: p_out = p2 == c2(p1) ? ZERO : p2 == ZERO ? p1 : NAR;
    endcase
  end
endmodule: lut_add

module lut_sub
  import ppu_pkg::*;
#(
  parameter N = -1
) (
  input   posit_t p1,
  input   posit_t p2,
  output  posit_t p_out
);

  always_comb begin
    case (p1)
      ZERO:    p_out = (p2 == ZERO) || (p2 == NAR) ? p2 : c2(p2);
      NAR:     p_out = NAR;
      default: p_out = p2 == p1 ? ZERO : p2 == ZERO ? p1 : NAR;
    endcase
  end
endmodule: lut_sub

module lut_div
  import ppu_pkg::*;
#(
  parameter N = -1
) (
  input   posit_t p1,
  input   posit_t p2,
  output  posit_t p_out
);

  always_comb begin
    case (p1)
      ZERO:    p_out = (p2 == NAR || p2 == ZERO) ? NAR : ZERO;
      NAR:     p_out = NAR;
      default: p_out = NAR;
    endcase
  end
endmodule: lut_div
module total_exponent 
  import ppu_pkg::*;
#(
  parameter N  = -1,
  parameter ES = -1
) (
  input  [ K_BITS-1:0]  k_i,
input  [     ES-1:0]  exp_i,
output exponent_t     total_exp_o
);


assign total_exp_o = $signed(k_i) >= 0 ? (k_i << ES) + exp_i : (-($signed(-k_i) << ES) + exp_i);

  endmodule: total_exponent
module ops 
  import ppu_pkg::*;
#(
  parameter N = -1
) (
  input logic             clk_i,
  input logic             rst_i,
  input operation_e       op_i,
  input fir_t             fir1_i,
  input fir_t             fir2_i,
  input fir_t             fir3_i,
  output ops_out_meta_t   ops_result_o
);

  
  wire [FRAC_FULL_SIZE-1:0] frac_out;

  logic sign_out;
  exponent_t te_out;
  wire [FRAC_FULL_SIZE-1:0] frac_full;

  wire frac_truncated;

  core_op #(
    .TE_BITS          (TE_BITS),
    .MANT_SIZE        (MANT_SIZE),
    .FRAC_FULL_SIZE   (FRAC_FULL_SIZE)
  ) core_op_inst (
    .clk_i            (clk_i),
    .rst_i            (rst_i),
    .op_i             (op_i),
    .fir1_i           (fir1_i),
    .fir2_i           (fir2_i),
    .fir3_i           (fir3_i),
    .te_o             (te_out),
    .frac_o           (frac_out),
    .frac_truncated_o (frac_truncated)
  );

  sign_decisor sign_decisor (
    .clk_i            (clk_i),
    .rst_i            (rst_i),
    .sign1_i          (fir1_i.sign),
    .sign2_i          (fir2_i.sign),
    .sign3_i          (fir3_i.sign),
    .op_i             (op_i),
    .sign_o           (sign_out)
  );
  
  assign ops_result_o.long_fir = {sign_out, te_out, frac_out};
  assign ops_result_o.frac_truncated = frac_truncated;

endmodule: ops
module core_op 
  import ppu_pkg::*;
#(
  parameter TE_BITS = -1,
  parameter MANT_SIZE = -1,
  parameter FRAC_FULL_SIZE = -1
) (
  input                         clk_i,
  input                         rst_i,
  input operation_e             op_i,
  input fir_t                   fir1_i,
  input fir_t                   fir2_i,
  input fir_t                   fir3_i,
  
    output exponent_t             te_o,
  output [(FRAC_FULL_SIZE)-1:0] frac_o,
  output                        frac_truncated_o
);

  wire [(MANT_ADD_RESULT_SIZE)-1:0] mant_out_add_sub;
  wire [(MANT_MUL_RESULT_SIZE)-1:0] mant_out_mul;
  wire [(MANT_DIV_RESULT_SIZE)-1:0] mant_out_div;


  exponent_t te_out_add_sub, te_out_mul, te_out_div;
  wire frac_truncated_add_sub, frac_truncated_mul, frac_truncated_div;

  core_add_sub #(
    .TE_BITS                (TE_BITS),
    .MANT_SIZE              (MANT_SIZE),
    .MANT_ADD_RESULT_SIZE   (MANT_ADD_RESULT_SIZE)
  ) core_add_sub_inst (
    .clk_i                  (clk_i),
    .rst_i                  (rst_i),
    .te1_i                  (fir1_i.total_exponent),
    .te2_i                  (fir2_i.total_exponent),
    .mant1_i                (fir1_i.mant),
    .mant2_i                (fir2_i.mant),
    .have_opposite_sign_i   (fir1_i.sign ^ fir2_i.sign),
    .mant_o                 (mant_out_add_sub),
    .te_o                   (te_out_add_sub),
    .frac_truncated_o       (frac_truncated_add_sub)
  );

  core_mul #(
    .TE_BITS                (TE_BITS),
    .MANT_SIZE              (MANT_SIZE),
    .MANT_MUL_RESULT_SIZE   (MANT_MUL_RESULT_SIZE)
  ) core_mul_inst (
    .clk_i                  (clk_i),
    .rst_i                  (rst_i),
    .te1_i                  (fir1_i.total_exponent),
    .te2_i                  (fir2_i.total_exponent),
    .mant1_i                (fir1_i.mant),
    .mant2_i                (fir2_i.mant),
    .mant_o                 (mant_out_mul),
    .te_o                   (te_out_mul),
    .frac_truncated_o       (frac_truncated_mul)
  );

  core_div #(
    .TE_BITS                (TE_BITS),
    .MANT_SIZE              (MANT_SIZE),
    .MANT_DIV_RESULT_SIZE   (MANT_DIV_RESULT_SIZE)
  ) core_div_inst (
    .clk_i                  (clk_i),
    .rst_i                  (rst_i),
    .te1_i                  (fir1_i.total_exponent),
    .te2_i                  (fir2_i.total_exponent),
    .mant1_i                (fir1_i.mant),
    .mant2_i                (fir2_i.mant),
    .mant_o                 (mant_out_div),
    .te_o                   (te_out_div),
    .frac_truncated_o       (frac_truncated_div)
  );


  wire [(FRAC_FULL_SIZE)-1:0] mant_out_core_op;
  assign mant_out_core_op = (op_i == ADD || op_i == SUB)
    ? mant_out_add_sub << (FRAC_FULL_SIZE - MANT_ADD_RESULT_SIZE) : op_i == MUL
    ? mant_out_mul << (FRAC_FULL_SIZE - MANT_MUL_RESULT_SIZE) : 
      mant_out_div;


      assign frac_o = op_i == DIV
    ? mant_out_core_op : 
      mant_out_core_op << 2;

  assign te_o = (op_i == ADD || op_i == SUB)
    ? te_out_add_sub : op_i == MUL
    ? te_out_mul : 
      te_out_div;

  assign frac_truncated_o = op_i == MUL
    ? frac_truncated_mul : op_i == DIV
    ? frac_truncated_div : 
      frac_truncated_add_sub;

  
  
  

endmodule: core_op
module core_add_sub 
    import ppu_pkg::*;
#(
  parameter TE_BITS = -1,
  parameter MANT_SIZE = -1,
  parameter MANT_ADD_RESULT_SIZE = -1
) (
  input logic                         clk_i,
  input logic                         rst_i,
  input exponent_t                    te1_i,
  input exponent_t                    te2_i,
  input  [             MANT_SIZE-1:0] mant1_i,
  input  [             MANT_SIZE-1:0] mant2_i,
  input                               have_opposite_sign_i,
  output [(MANT_ADD_RESULT_SIZE)-1:0] mant_o,
  output exponent_t                   te_o,
  output                              frac_truncated_o
);

  function [(MANT_SIZE+MAX_TE_DIFF)-1:0] _c2(input [(MANT_SIZE+MAX_TE_DIFF)-1:0] a);
    _c2 = ~a + 1'b1;
  endfunction


  logic have_opposite_sign_st0, have_opposite_sign_st1;
  assign have_opposite_sign_st0 = have_opposite_sign_i;

  exponent_t te1, te2_st0, te2_st1;
  wire [MANT_SIZE-1:0] mant1, mant2;
  assign {te1, te2_st0} = {te1_i, te2_i};
  assign {mant1, mant2} = {mant1_i, mant2_i};


  exponent_t te_diff_st0, te_diff_st1;
  assign te_diff_st0 = $signed(te1) - $signed(te2_st0);

  wire [(MANT_SIZE+MAX_TE_DIFF)-1:0] mant1_upshifted, mant2_upshifted;
  assign mant1_upshifted = mant1 << MAX_TE_DIFF;
  assign mant2_upshifted = (mant2 << MAX_TE_DIFF) >> max(0, te_diff_st0);

  logic [(MANT_ADD_RESULT_SIZE)-1:0] mant_sum_st0, mant_sum_st1;
  assign mant_sum_st0 = mant1_upshifted + (have_opposite_sign_i ? _c2(
      mant2_upshifted
  ) : mant2_upshifted);


  wire [(MANT_ADD_RESULT_SIZE)-1:0] mant_out_core_add;
  exponent_t te_diff_out_core_add;
  core_add #(
    .TE_BITS              (TE_BITS),
    .MANT_ADD_RESULT_SIZE (MANT_ADD_RESULT_SIZE)
  ) core_add_inst (
    .mant_i               (mant_sum_st1),
    .te_diff_i            (te_diff_st1),
    .new_mant_o           (mant_out_core_add),
    .new_te_diff_o        (te_diff_out_core_add),
    .frac_truncated_o     (frac_truncated_o)
  );


  wire [(MANT_SUB_RESULT_SIZE)-1:0] mant_out_core_sub;
  exponent_t te_diff_out_core_sub;
  core_sub #(
    .TE_BITS              (TE_BITS),
    .MANT_SUB_RESULT_SIZE (MANT_SUB_RESULT_SIZE)
  ) core_sub_inst (
    .mant                 (mant_sum_st1[MANT_SUB_RESULT_SIZE-1:0]),
    .te_diff              (te_diff_st1),
    .new_mant             (mant_out_core_sub),
    .new_te_diff          (te_diff_out_core_sub)
  );

  exponent_t te_diff_updated;
  assign te_diff_updated = have_opposite_sign_st1 ? te_diff_out_core_sub : te_diff_out_core_add;

  assign mant_o = have_opposite_sign_st1 ? {mant_out_core_sub  } : mant_out_core_add;

  assign te_o = te2_st1 + te_diff_updated;


assign te_diff_st1 = te_diff_st0;
  assign mant_sum_st1 = mant_sum_st0;
  assign have_opposite_sign_st1 = have_opposite_sign_st0;
  assign te2_st1 = te2_st0;
endmodule: core_add_sub
module core_add 
  import ppu_pkg::*;
#(
  parameter TE_BITS = -1,
  parameter MANT_ADD_RESULT_SIZE = -1
) (
  input  [(MANT_ADD_RESULT_SIZE)-1:0] mant_i,
  input  exponent_t                   te_diff_i,
  output [(MANT_ADD_RESULT_SIZE)-1:0] new_mant_o,
  output exponent_t                   new_te_diff_o,
  output logic                        frac_truncated_o
);

  wire mant_carry;
  assign mant_carry = mant_i[MANT_ADD_RESULT_SIZE-1];

  assign new_mant_o = mant_carry == 1'b1 ? mant_i >> 1 : mant_i;
  assign new_te_diff_o = mant_carry == 1'b1 ? te_diff_i + 1 : te_diff_i;

  assign frac_truncated_o = mant_carry && (mant_i & 1);

endmodule: core_add
module core_sub 
  import ppu_pkg::*;
#(
  parameter TE_BITS = -1,
  parameter MANT_SUB_RESULT_SIZE = -1
) (
  input  [(MANT_SUB_RESULT_SIZE)-1:0] mant,
  input   exponent_t                  te_diff,
  output [(MANT_SUB_RESULT_SIZE)-1:0] new_mant,
  output  exponent_t                  new_te_diff
);

  wire [($clog2(MANT_SUB_RESULT_SIZE))-1:0] leading_zeros;

  

  wire is_valid;  
  lzc #(
    .NUM_BITS   (MANT_SUB_RESULT_SIZE)
  ) lzc_inst (
    .bits_i     (mant),
    .lzc_o      (leading_zeros),
    .valid_o    (is_valid)
  );

  assign new_te_diff = te_diff - leading_zeros;
  assign new_mant = (mant << leading_zeros);  
endmodule
module core_mul 
  import ppu_pkg::*;
#(
  parameter TE_BITS = -1,
  parameter MANT_SIZE = -1,
  parameter MANT_MUL_RESULT_SIZE = -1
) (
  input                             clk_i,
  input                             rst_i,
  input  exponent_t                 te1_i,
  input  exponent_t                 te2_i,
  input  [           MANT_SIZE-1:0] mant1_i,
  input  [           MANT_SIZE-1:0] mant2_i,
  output [MANT_MUL_RESULT_SIZE-1:0] mant_o,   output exponent_t                 te_o,
  output                            frac_truncated_o
);

  exponent_t te_sum_st0, te_sum_st1;
  assign te_sum_st0 = te1_i + te2_i;

  wire [MANT_SUB_RESULT_SIZE-1:0] mant_mul;


  wire mant_carry;
  assign mant_carry = mant_mul[MANT_MUL_RESULT_SIZE-1];

  assign te_o = mant_carry == 1'b1 ? te_sum_st1 + 1'b1 : te_sum_st1;
  assign mant_o = mant_carry == 1'b1 ? mant_mul >> 1 : mant_mul;

  assign frac_truncated_o = mant_carry && (mant_mul & 1);



assign te_sum_st1 = te_sum_st0;
  assign mant_mul = mant1_i * mant2_i;
endmodule: core_mul
module core_div
  import ppu_pkg::*;
#(
  parameter TE_BITS = -1,
  parameter MANT_SIZE = -1,
  parameter MANT_DIV_RESULT_SIZE = -1
) (
  input                               clk_i,
  input                               rst_i,
  input  exponent_t                   te1_i,
  input  exponent_t                   te2_i,
  input  [             MANT_SIZE-1:0] mant1_i,
  input  [             MANT_SIZE-1:0] mant2_i,
  output [(MANT_DIV_RESULT_SIZE)-1:0] mant_o,
  output exponent_t                   te_o,
  output                              frac_truncated_o
);

  logic [MANT_SIZE-1:0] mant1_st0, mant1_st1;
  assign mant1_st0 = mant1_i;

  exponent_t te_diff_st0, te_diff_st1;
  assign te_diff_st0 = te1_i - te2_i;

  wire [(MANT_DIV_RESULT_SIZE)-1:0] mant_div;

  

  wire [(3*MANT_SIZE-4)-1:0] mant2_reciprocal;


initial $display("***** NOT using DIV with LUT *****");

  fast_reciprocal #(
    .SIZE               (MANT_SIZE)
  ) fast_reciprocal_inst (
    .fraction           (mant2_i),
    .one_over_fraction  (mant2_reciprocal)
  );
wire [(2*MANT_SIZE)-1:0] x1;

`define NEWTON_RAPHSON
initial $display("***** Using NR *****");
  
  newton_raphson #(
    .NR_SIZE (N)
  ) newton_raphson_inst (
    .clk_i  (clk_i),
    .rst_i  (rst_i),
    .num_i  (mant2_i),
    .x0_i   (mant2_reciprocal),
    .x1_o   (x1)
  );
assign mant_div = mant1_st1 * x1;


  wire mant_div_less_than_one;
  assign mant_div_less_than_one = (mant_div & (1 << (3 * MANT_SIZE - 2))) == 0;

  assign mant_o = mant_div_less_than_one ? mant_div << 1 : mant_div;
  assign te_o = mant_div_less_than_one ? te_diff_st1 - 1 : te_diff_st1;

  assign frac_truncated_o = 1'b0;


assign te_diff_st1 = te_diff_st0;
  assign mant1_st1   = mant1_st0;
endmodule: core_div
module fast_reciprocal 
  import ppu_pkg::*;
#(
  parameter SIZE = -1
) (
  input  [    (SIZE)-1:0] fraction,
  output [(3*SIZE-4)-1:0] one_over_fraction
);

  wire [(SIZE)-1:0] i_data;
  wire [(3*SIZE-3)-1:0] o_data;

  assign i_data = fraction >> 1;

  reciprocal_approx #(
    .SIZE     (SIZE)
  ) reciprocal_approx_inst (
    .i_data   (i_data),
    .o_data   (o_data)
  );

  assign one_over_fraction = o_data >> 1;

endmodule: fast_reciprocal
module reciprocal_approx 
  import ppu_pkg::*;
  #(
    parameter SIZE = -1
  )(
    input [SIZE-1:0]                   i_data,
    output [(3*SIZE-1-2)-1:0]          o_data
  );

  reg [(SIZE)-1:0] a, b;
  reg [(2*SIZE-1)-1:0] c, d;
  reg [(3*SIZE-1)-1:0] e;
  reg [(3*SIZE-1-2)-1:0] out;

  assign a = i_data;


    wire [(SIZE)-1:0] fx_1_466  = fx_1_466___N16;
  wire [(2*SIZE-1)-1:0] fx_1_0012 = fx_1_0012___N16;


  assign b = fx_1_466 - a;
  assign c = (($signed(a) * $signed(b)) << 1) >> 1;
  assign d = fx_1_0012 - c;
  assign e = $signed(d) * $signed(b);
  assign out = e;

    assign o_data = out;

endmodule: reciprocal_approx















module newton_raphson 
  import ppu_pkg::MS;
#(
  parameter NR_SIZE = -1
)(
  input                   clk_i,
  input                   rst_i,
  input   [(MS)-1:0]      num_i,
  input   [(3*MS-4)-1:0]  x0_i,
  output  [(2*MS)-1:0]    x1_o
);
  
  


  wire [(4*MS-3)-1:0] _num_times_x0;
  assign _num_times_x0 = (num_i * x0_i) >> (2*MS - 4);
  
  
  logic [(2*MS)-1:0] num_times_x0_st0, num_times_x0_st1;
  assign num_times_x0_st0 = _num_times_x0;


    wire [(2*MS)-1:0] fx_2 = ppu_pkg::fx_2___N16;

  wire [(2*MS)-1:0] two_minus_num_x0;
  assign two_minus_num_x0 = fx_2 - num_times_x0_st1;


  logic [(2*MS)-1:0] x0_on_2n_bits_st0, x0_on_2n_bits_st1;
  assign x0_on_2n_bits_st0 = x0_i >> (MS - 4);

  wire [(4*MS)-1:0] _x1;
  assign _x1 = x0_on_2n_bits_st1 * two_minus_num_x0;

    assign x1_o = _x1 >> (2*MS - 2);


  assign num_times_x0_st1 = num_times_x0_st0;
  assign x0_on_2n_bits_st1 = x0_on_2n_bits_st0;
endmodule: newton_raphson
module pack_fields 
  import ppu_pkg::*;
#(
  parameter N  = -1,
  parameter ES = -1
) (
  input [FRAC_FULL_SIZE-1:0]  frac_full_i,
  input exponent_t            total_exp_i,
  input                       frac_truncated_i, 
  output [   K_BITS-1:0] k_o,
output [       ES-1:0] next_exp_o,
output [MANT_SIZE-1:0] frac_o,

    output round_bit,
  output sticky_bit,
  output k_is_oob,
  output non_zero_frac_field_size
);

  wire [K_BITS-1:0] k_unpacked;

wire [ES-1:0] exp_unpacked;
unpack_exponent #(
    .N          (N),
    .ES         (ES)
  ) unpack_exponent_inst (
    .total_exp_i(total_exp_i),
    .k_o        (k_unpacked)
,
    .exp_o      (exp_unpacked)
);


  wire [K_BITS-1:0] regime_k;
  assign regime_k = ($signed(
      k_unpacked
  ) <= (N - 2) && $signed(
      k_unpacked
  ) >= -(N - 2)) ? $signed(
      k_unpacked
  ) : ($signed(
      k_unpacked
  ) >= 0 ? N - 2 : -(N - 2));

  assign k_is_oob = k_unpacked != regime_k;

  wire [REG_LEN_BITS-1:0] reg_len;
  assign reg_len = $signed(regime_k) >= 0 ? regime_k + 2 : -$signed(regime_k) + 1;


  wire [MANT_LEN_BITS-1:0] frac_len;    assign frac_len = N - 1 - ES - reg_len;

wire [(ES+1)-1:0] es_actual_len;    assign es_actual_len = min(ES, N - 1 - reg_len);


  wire [ES-1:0] exp1;
  assign exp1 = exp_unpacked >> max(0, ES - es_actual_len);
wire [(S+2)-1:0] frac_len_diff;
  assign frac_len_diff = FRAC_FULL_SIZE - $signed(frac_len);


  compute_rouding #(
    .N                (N),
    .ES               (ES)
  ) compute_rouding_inst (
    .frac_len_i       (frac_len),
    .frac_full_i      (frac_full_i),
    .frac_len_diff_i  (frac_len_diff),
    .k_i              (regime_k),
.exp_i            (exp_unpacked),
.frac_truncated_i (frac_truncated_i),
    .round_bit_o      (round_bit),
    .sticky_bit_o     (sticky_bit)
  );

  assign k_o = regime_k;  
wire [ES-1:0] exp2;
  assign exp2 = exp1 << (ES - es_actual_len);
assign frac_o = frac_full_i >> frac_len_diff;

  assign non_zero_frac_field_size = $signed(frac_len) >= 0;

assign next_exp_o = exp2;
endmodule: pack_fields
module unpack_exponent 
  import ppu_pkg::*;
#(
  parameter N  = -1,
  parameter ES = -1
) (
  input  exponent_t     total_exp_i,
  output [ K_BITS-1:0]  k_o
, output [     ES-1:0]  exp_o
);

  assign k_o = total_exp_i >> ES;

assign exp_o = total_exp_i - ((1 << ES) * k_o);
endmodule: unpack_exponent
module compute_rouding
  import ppu_pkg::*;
#(
  parameter N  = -1,
  parameter ES = -1
) (
  input  [ MANT_LEN_BITS-1:0] frac_len_i,
  input  [FRAC_FULL_SIZE-1:0] frac_full_i,
  input  [         (S+2)-1:0] frac_len_diff_i,
  input  [        K_BITS-1:0] k_i,
input  [            ES-1:0] exp_i,
input                       frac_truncated_i,
  output                      round_bit_o,
  output                      sticky_bit_o
);

  wire [(3*MANT_SIZE+2)-1:0] _tmp0, _tmp1, _tmp2, _tmp3;

  assign _tmp0 = (1 << (frac_len_diff_i - 1));
  assign _tmp1 = frac_full_i & _tmp0;

assign round_bit_o = $signed(
    frac_len_i
  ) >= 0 ? _tmp1 != 0 : $signed(
    k_i
  ) == N - 2 - ES ? exp_i > 0 && $unsigned(
    frac_full_i
  ) > 0 : $signed(
    k_i
  ) == -(N - 2) ? (                
    exp_i
  ) > 0 : 1'b0;
assign _tmp2 = ((1 << (frac_len_diff_i - 1)) - 1);
  assign _tmp3 = frac_full_i & _tmp2;

  assign sticky_bit_o = $signed(frac_len_i) >= 0 ? (_tmp3 != 0) || frac_truncated_i : 1'b0;

endmodule: compute_rouding
module posit_unpack
  import ppu_pkg::*;
#(
  parameter N = 5,
  parameter ES = 0
)(
  input posit_t               bits_i,
  
  output                      sign_o,
  output                      reg_s_o,
  output [REG_LEN_BITS-1:0]   reg_len_o,
  output [K_BITS-1:0]       k_o,
output [ES-1:0]             exp_o,
output [MANT_SIZE-1:0]      mant_o
);

  assign sign_o = bits_i[N-1];

    wire [N-1:0] u_bits;
  assign u_bits = sign_o == 0 ? bits_i : c2(bits_i);

  wire [S-1:0] leading_set,
               leading_set_2;

    assign reg_s_o = u_bits[N-2];



      
      wire is_special_case;
      assign is_special_case = bits_i == { {1{1'b1}}, {N-2{1'b0}}, {1{1'b1}} };


      assign leading_set_2 = is_special_case ? (N-1) : leading_set;                                                                                                                                     
  assign k_o = reg_s_o == 1 ? leading_set_2 - 1 : c2(leading_set_2);


  assign reg_len_o = reg_s_o == 1 ? k_o + 2 : c2(k_o) + 1;


assign exp_o = (u_bits << (1 + reg_len_o)) >> (N - ES);
wire [(S+1)-1:0] mant_len;
  assign mant_len = N - 1 - reg_len_o - ES;

  wire [FRAC_SIZE-1:0] frac;
  assign frac = (u_bits << (N - mant_len)) >> (N - mant_len);


  parameter MSB = 1 << (MANT_SIZE - 1);
    assign mant_o = MSB | (frac << (MANT_SIZE-mant_len-1)); 

  wire [N-1:0] bits_cls_in = sign_o == 0 ? u_bits : ~u_bits;

  wire val = bits_cls_in[N-2];


                  
  wire [S-1:0] leading_set_out_lzc;
  wire lzc_is_valid;

  lzc #(
    .NUM_BITS(N)
  ) lzc_inst (
    .bits_i(
        (val == 1'b0 ? bits_cls_in : ~bits_cls_in) << 1
    ),
    .lzc_o(leading_set_out_lzc),
    .valid_o(lzc_is_valid)
  );

  assign leading_set = lzc_is_valid == 1'b1 ? leading_set_out_lzc : N - 1;
endmodule: posit_unpack



module posit_decoder 
  import ppu_pkg::*;
#(
  parameter N  = -1,    parameter ES = -1   ) (
  input posit_t   bits_i,
  output fir_t    fir_o
);

  wire                    _reg_s;    wire [REG_LEN_BITS-1:0] _reg_len;  
  wire [K_BITS-1:0] k;
wire [ES-1:0] exp;
logic sign;
  exponent_t total_exponent;
  wire [MANT_SIZE-1:0] mant;

  posit_unpack #(
    .N          (N),
    .ES         (ES)
  ) posit_unpack_inst (
    .bits_i     (bits_i),
    .sign_o     (sign),
    .reg_s_o    (_reg_s),
    .reg_len_o  (_reg_len),
    .k_o        (k),
.exp_o      (exp),
.mant_o     (mant)
  );

  total_exponent #(
    .N          (N),
    .ES         (ES)
  ) total_exponent_inst (
    .k_i        (k),
.exp_i      (exp),
.total_exp_o(total_exponent)
  );

  assign fir_o.sign = sign;
  assign fir_o.total_exponent = total_exponent;
  assign fir_o.mant = mant;

endmodule: posit_decoder
module posit_encoder 
  import ppu_pkg::*;
#(
    parameter N = 4,
    parameter ES = 1
)(
    input                           is_zero_i,
    input                           is_nar_i,
    input                           sign,
    input [K_BITS-1:0]              k,
input [ES-1:0]                  exp,
input [MANT_SIZE-1:0]           frac,
    output [N-1:0]                  posit
  );

  wire [REG_LEN_BITS-1:0] reg_len;
  assign reg_len = $signed(k) >= 0 ? k + 2 : -$signed(k) + 1;

  wire [N-1:0] bits_assembled;

  wire [N:0] regime_bits; 
  assign regime_bits = is_negative(k) ? 1 : (shl(1, (k + 1)) - 1) << 1;


assign bits_assembled = (
      shl(sign, N-1)
    + shl(regime_bits, N - 1 - reg_len)
+ shl(exp, N - 1 - reg_len - ES)
+ frac
  );

  assign posit =
    sign == 0
    ? bits_assembled : c2(bits_assembled & ~(1 << (N - 1)));

  

endmodule: posit_encoder
module lzc #(
  parameter NUM_BITS = -1
) (
  input  [        NUM_BITS-1:0] bits_i,
  output [$clog2(NUM_BITS)-1:0] lzc_o,
  output                        valid_o
);
    lzc_internal #(
    .NUM_BITS   (NUM_BITS)
  ) l1 (
    .in         (bits_i),
    .out        (lzc_o),
    .vld        (valid_o)
  );
endmodule: lzc

module lzc_internal #(
  parameter NUM_BITS = 8
) (
  input  [        NUM_BITS-1:0] in,
  output [$clog2(NUM_BITS)-1:0] out,
  output                        vld
);
  
  localparam S = $clog2(NUM_BITS);

  generate
    if (NUM_BITS == 2) begin : gen_blk1
      assign vld = |in;
      assign out = ~in[1] & in[0];
    end else if (NUM_BITS & (NUM_BITS - 1)) begin : gen_blk2
      lzc_internal #(
        .NUM_BITS     (1 << S)
      ) lzc_internal (
        .in           ({in, {((1 << S) - NUM_BITS) {1'b0}}}),
        .out          (out),
        .vld          (vld)
      );
    end else begin : gen_blk3
      wire [S-2:0] out_l, out_h;
      wire out_vl, out_vh;

      lzc_internal #(
        .NUM_BITS     (NUM_BITS >> 1)
      ) lzc_internal_l (
        .in           (in[(NUM_BITS>>1)-1:0]),
        .out          (out_l),
        .vld          (out_vl)
      );

      lzc_internal #(
        .NUM_BITS     (NUM_BITS >> 1)
      ) lzc_internal_h (
        .in           (in[NUM_BITS-1 : NUM_BITS>>1]),
        .out          (out_h),
        .vld          (out_vh)
      );

      assign vld = out_vl | out_vh;
      assign out = out_vh ? {1'b0, out_h} : {out_vl, out_l};
    end
  endgenerate
endmodule: lzc_internal
module round_posit
#(
  parameter N = 10
) (
  input  [N-1:0] posit,
  input          round_bit,
  input          sticky_bit,
  input          k_is_oob,
  input          non_zero_frac_field_size,
  output [N-1:0] posit_rounded
);

  wire guard_bit;
  assign guard_bit = posit[0];

  assign posit_rounded =
    !k_is_oob && round_bit && (!non_zero_frac_field_size || (guard_bit || sticky_bit))
    ? posit + 1'b1 : posit;

endmodule: round_posit
module sign_decisor
(
  input logic                 clk_i,
  input logic                 rst_i,
  input logic                 sign1_i,
  input logic                 sign2_i,
  input logic                 sign3_i,
  input ppu_pkg::operation_e  op_i,
  output logic                sign_o
);

  logic sign1_st1, sign2_st1;

    assign sign_o = 
    (op_i == ppu_pkg::ADD || op_i == ppu_pkg::SUB) 
    ? sign1_st1 : 
      sign1_st1 ^ sign2_st1;

assign sign1_st1 = sign1_i;
  assign sign2_st1 = sign2_i;
endmodule: sign_decisor
module set_sign 
  import ppu_pkg::c2;
#(
  parameter N = 9
) (
  input  [N-1:0] posit_in,
  input          sign,
  output [N-1:0] posit_out
);

  assign posit_out = sign == 0 ? posit_in : c2(posit_in);

endmodule: set_sign
module ppu
  import ppu_pkg::OP_BITS;
#(
  parameter WORD = 32,
  parameter N = 16,
  parameter ES = 1
) (
  input logic                           clk_i,
  input logic                           rst_i,
  input logic                           in_valid_i,
  input logic                [WORD-1:0] operand1_i,
  input logic                [WORD-1:0] operand2_i,
  input logic                [WORD-1:0] operand3_i,
  input ppu_pkg::operation_e            op_i,
  output logic               [WORD-1:0] result_o,
  output logic                          out_valid_o
);

  wire stall;
  ppu_pkg::fir_t posit_fir;
  ppu_pkg::posit_t p1, p2, p3, posit;

  assign p1 = operand1_i[N-1:0];
  assign p2 = operand2_i[N-1:0];
  assign p3 = operand3_i[N-1:0];


  ppu_core_ops #(
    .N            (N),
    .ES           (ES)
  ) ppu_core_ops_inst (
    .clk_i        (clk_i),
    .rst_i        (rst_i),
    .p1_i         (p1),
    .p2_i         (p2),
    .p3_i         (p3),
    .op_i         (op_i),
    .op_o         (),
    .stall_i      (stall),
  .pout_o       (posit)
  );

  assign result_o = posit;
  
    assign out_valid_o = in_valid_i;

endmodule: ppu
module pipeline #(
  parameter PIPE_DEPTH = 2,
  parameter DATA_WIDTH = 32 
)(
  input logic                     clk_i,
  input logic                     rst_i,
  input logic   [DATA_WIDTH-1:0]  data_in,
  output logic  [DATA_WIDTH-1:0]  data_out
);

  
  generate
    if (PIPE_DEPTH == 0) begin
      assign data_out = data_in;
    end else begin
            logic [DATA_WIDTH-1:0] pipeline_reg [PIPE_DEPTH-1:0] ;

      always_ff @(posedge clk_i) begin
        if (rst_i) begin
          for (int i = 0; i < PIPE_DEPTH; i++) begin
            pipeline_reg[i] <= 'b0;
          end
        end else begin
          pipeline_reg[0] <= data_in; 
          for (int i = 1; i < PIPE_DEPTH; i++) begin
            pipeline_reg[i] <= pipeline_reg[i-1];
          end
        end
      end

      assign data_out = pipeline_reg[PIPE_DEPTH-1];

    end
  endgenerate
  
  
endmodule: pipeline







    







module ppu_top 
  import ppu_pkg::*;
#(
  parameter WORD = 32,
parameter N = 16,
  parameter ES = 1
) (
  input  logic                    clk_i,
  input  logic                    rst_i,
  input  logic                    in_valid_i,
  input  logic        [WORD-1:0]  operand1_i,
  input  logic        [WORD-1:0]  operand2_i,
  input  logic        [WORD-1:0]  operand3_i,
  input  logic		  [OP_BITS-1:0]  op_i,
  output logic        [WORD-1:0]  result_o,
  output logic                    out_valid_o
);

  logic [WORD-1:0] operand1_st0, operand2_st0, operand3_st0;

  logic [WORD-1:0] result_st0,
                   result_st1;
  logic [OP_BITS-1:0] op_st0;

  logic in_valid_st0;
        
  logic out_valid_st0,
        out_valid_st1;

  

  ppu #(
    .WORD           (WORD),
    .N              (N),
    .ES             (ES)
  ) ppu_inst (
    .clk_i          (clk_i),
    .rst_i          (rst_i),
    .in_valid_i     (in_valid_st0),
    .operand1_i     (operand1_st0),
    .operand2_i     (operand2_st0),
    .operand3_i     (operand3_st0),
    .op_i           (operation_e'(op_st0)),
    .result_o       (result_st0),
    .out_valid_o    (out_valid_st0)
);


  
  pipeline #(
    .PIPE_DEPTH   (1),
    .DATA_WIDTH   ($bits(in_valid_i) + $bits(op_i) + 3*$bits(operand1_i))
  ) pipeline_in (
    .clk_i        (clk_i),
    .rst_i        (rst_i),
    .data_in      ({in_valid_i,   op_i,   operand1_i,   operand2_i,   operand3_i}),
    .data_out     ({in_valid_st0, op_st0, operand1_st0, operand2_st0, operand3_st0})
  );

  pipeline #(
    .PIPE_DEPTH   (1),
    .DATA_WIDTH   ($bits(result_st0) + $bits(out_valid_st0))
  ) pipeline_out (
    .clk_i        (clk_i),
    .rst_i        (rst_i),
    .data_in      ({result_st0, out_valid_st0}),
    .data_out     ({result_o,   out_valid_o})
  );

  

endmodule: ppu_top


module clk_gen #(
  parameter CLK_FREQ = 1 )(
  output logic clk_o
);

  initial begin 
    #1.23;
    clk_o = 0;
    forever #((1000.0/CLK_FREQ) / 2.0)  clk_o = !clk_o;
  end

        
endmodule: clk_gen
module tb_ppu #(
  parameter CLK_FREQ = 100
);

  import ppu_pkg::*;

  parameter WORD = 32;
  parameter N = 16;
  parameter ES = 1;
  parameter FSIZE = 0;

  localparam ASCII_SIZE = 300;

  logic                                 clk_i;
  logic                                 rst_i;
  logic                                 in_valid_i;
  logic                   [WORD-1:0]    operand1_i;
  logic                   [WORD-1:0]    operand2_i;
  logic                   [WORD-1:0]    operand3_i;
  ppu_pkg::operation_e                  op_i;
  logic                 [ASCII_SIZE:0]  op_i_ascii;
  wire                  [WORD-1:0]      result_o;
  wire                                  out_valid_o;


  logic [ASCII_SIZE-1:0]  operand1_i_ascii,                             operand2_i_ascii,                             operand3_i_ascii,                             result_o_ascii,                               result_gt_ascii;    

  logic [WORD-1:0] out_ground_truth;
  logic [N-1:0] pout_hwdiv_expected;
  logic diff_out_ground_truth, diff_pout_hwdiv_exp, pout_off_by_1;
  logic [  N:0] test_no;

  logic [100:0] count_errors;


  clk_gen #(
    .CLK_FREQ     (CLK_FREQ)
  ) clk_gen_i (
    .clk_o        (clk_i)
  );  


  ppu_top #(
    .WORD         (WORD),
    .N            (N),
    .ES           (ES)
  ) ppu_top_inst (
    .clk_i        (clk_i),
    .rst_i        (rst_i),
    .in_valid_i   (in_valid_i),
    .operand1_i   (operand1_i),
    .operand2_i   (operand2_i),
    .operand3_i   (operand3_i),
    .op_i         (op_i),
    .result_o     (result_o),
    .out_valid_o  (out_valid_o)
  );


  initial $display("N = %d", N);
  initial $display("ES = %d", ES);
  initial $display("F = %d", FSIZE);
  initial $display("WORD = %d", WORD);
  initial $display("CLK_FREQ = %d MHz", CLK_FREQ);


    
  initial rst_i = 0;
  
  
  always @(*) begin
    diff_out_ground_truth = result_o === out_ground_truth ? 0 : 1'bx;
    pout_off_by_1 = abs(result_o - out_ground_truth) == 0 ? 0 :
                    abs(result_o - out_ground_truth) == 1 ? 1 : 'bx;
    diff_pout_hwdiv_exp = (op_i != DIV) ? 'hz : 
                          result_o === pout_hwdiv_expected ? 0 : 1'bx;
  end


      integer f;
  initial f = $fopen("ppu_output.log", "w");

  always @(posedge clk_i) begin
    if (in_valid_i) $fwrite(f, "i %h %h %h %t\n", operand1_i, op_i, operand2_i, $time);
  end

  always @(posedge clk_i) begin
    if (out_valid_o) $fwrite(f, "o %h %t\n", result_o, $time);
  end
  
  initial begin: vcd_file
        $dumpfile({"tb_ppu.vcd"});
    $dumpvars(0, tb_ppu);
  end

  initial begin: sequences
    in_valid_i = 1'b0;
    @(posedge clk_i);
  

                	
op_i = MUL;
op_i_ascii = "MUL";

@(negedge clk_i);
#1.5541;
test_no =                 1;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h9874;
	operand2_i_ascii =        "-7.7734375";
	result_gt_ascii =         "0";
	out_ground_truth =        16'h0000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 2;
	in_valid_i = 1'b1;
	operand1_i =              16'h8000;
	operand1_i_ascii =        "nan";
	operand2_i =              16'h381d;
	operand2_i_ascii =        "0.7535400390625";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 3;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h8000;
	operand2_i_ascii =        "nan";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 4;
	in_valid_i = 1'b0;
	operand1_i =              16'h0db3;
	operand1_i_ascii =        "0.044525146484375";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "0";
	out_ground_truth =        16'h0000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 5;
	in_valid_i = 1'b1;
	operand1_i =              16'he409;
	operand1_i_ascii =        "-0.18695068359375";
	operand2_i =              16'h8000;
	operand2_i_ascii =        "nan";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 6;
	in_valid_i = 1'b0;
	operand1_i =              16'h8000;
	operand1_i_ascii =        "nan";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 7;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "0";
	out_ground_truth =        16'h0000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 8;
	in_valid_i = 1'b1;
	operand1_i =              16'he382;
	operand1_i_ascii =        "-0.1951904296875";
	operand2_i =              16'h1c7e;
	operand2_i_ascii =        "0.1951904296875";
	result_gt_ascii =         "-0.0380859375";
	out_ground_truth =        16'hf320;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 9;
	in_valid_i = 1'b1;
	operand1_i =              16'h8001;
	operand1_i_ascii =        "-268435456.0";
	operand2_i =              16'hd3b4;
	operand2_i_ascii =        "-0.442138671875";
	result_gt_ascii =         "67108864.0";
	out_ground_truth =        16'h7ffe;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 10;
	in_valid_i = 1'b1;
	operand1_i =              16'hf43c;
	operand1_i_ascii =        "-0.03033447265625";
	operand2_i =              16'h702c;
	operand2_i_ascii =        "16.6875";
	result_gt_ascii =         "-0.5062255859375";
	out_ground_truth =        16'hcfcd;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 11;
	in_valid_i = 1'b1;
	operand1_i =              16'hd552;
	operand1_i_ascii =        "-0.4168701171875";
	operand2_i =              16'h698c;
	operand2_i_ascii =        "9.546875";
	result_gt_ascii =         "-3.97998046875";
	out_ground_truth =        16'ha029;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 12;
	in_valid_i = 1'b1;
	operand1_i =              16'hd60b;
	operand1_i_ascii =        "-0.40557861328125";
	operand2_i =              16'hfc39;
	operand2_i_ascii =        "-0.00347137451171875";
	result_gt_ascii =         "0.001407623291015625";
	out_ground_truth =        16'h0271;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 13;
	in_valid_i = 1'b1;
	operand1_i =              16'h679c;
	operand1_i_ascii =        "7.8046875";
	operand2_i =              16'h758e;
	operand2_i_ascii =        "44.4375";
	result_gt_ascii =         "347.0";
	out_ground_truth =        16'h7c5b;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 14;
	in_valid_i = 1'b1;
	operand1_i =              16'h14c8;
	operand1_i_ascii =        "0.099853515625";
	operand2_i =              16'h7f26;
	operand2_i_ascii =        "6528.0";
	result_gt_ascii =         "652.0";
	out_ground_truth =        16'h7d46;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 15;
	in_valid_i = 1'b1;
	operand1_i =              16'h4ea8;
	operand1_i_ascii =        "1.916015625";
	operand2_i =              16'hdb6d;
	operand2_i_ascii =        "-0.32147216796875";
	result_gt_ascii =         "-0.615966796875";
	out_ground_truth =        16'hcc4a;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 16;
	in_valid_i = 1'b1;
	operand1_i =              16'h1aad;
	operand1_i_ascii =        "0.16680908203125";
	operand2_i =              16'he85b;
	operand2_i_ascii =        "-0.122222900390625";
	result_gt_ascii =         "-0.0203857421875";
	out_ground_truth =        16'hf6c8;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 17;
	in_valid_i = 1'b1;
	operand1_i =              16'hc2be;
	operand1_i_ascii =        "-0.914306640625";
	operand2_i =              16'hed84;
	operand2_i_ascii =        "-0.0819091796875";
	result_gt_ascii =         "0.07489013671875";
	out_ground_truth =        16'h1196;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 18;
	in_valid_i = 1'b1;
	operand1_i =              16'h69e7;
	operand1_i_ascii =        "9.90234375";
	operand2_i =              16'hd937;
	operand2_i_ascii =        "-0.35601806640625";
	result_gt_ascii =         "-3.525390625";
	out_ground_truth =        16'ha3cc;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 19;
	in_valid_i = 1'b1;
	operand1_i =              16'h8599;
	operand1_i_ascii =        "-153.75";
	operand2_i =              16'he957;
	operand2_i_ascii =        "-0.114532470703125";
	result_gt_ascii =         "17.609375";
	out_ground_truth =        16'h7067;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 20;
	in_valid_i = 1'b1;
	operand1_i =              16'h7402;
	operand1_i_ascii =        "32.0625";
	operand2_i =              16'h0407;
	operand2_i_ascii =        "0.00395965576171875";
	result_gt_ascii =         "0.126953125";
	out_ground_truth =        16'h1820;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 21;
	in_valid_i = 1'b1;
	operand1_i =              16'h7ef9;
	operand1_i_ascii =        "3984.0";
	operand2_i =              16'h7fe9;
	operand2_i_ascii =        "589824.0";
	result_gt_ascii =         "268435456.0";
	out_ground_truth =        16'h7fff;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 22;
	in_valid_i = 1'b1;
	operand1_i =              16'h6e4d;
	operand1_i_ascii =        "14.30078125";
	operand2_i =              16'hbf00;
	operand2_i_ascii =        "-1.0625";
	result_gt_ascii =         "-15.1953125";
	out_ground_truth =        16'h90ce;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 23;
	in_valid_i = 1'b1;
	operand1_i =              16'h7146;
	operand1_i_ascii =        "21.09375";
	operand2_i =              16'h289e;
	operand2_i_ascii =        "0.3846435546875";
	result_gt_ascii =         "8.11328125";
	out_ground_truth =        16'h681d;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 24;
	in_valid_i = 1'b1;
	operand1_i =              16'hd721;
	operand1_i_ascii =        "-0.38861083984375";
	operand2_i =              16'h356e;
	operand2_i_ascii =        "0.669677734375";
	result_gt_ascii =         "-0.26025390625";
	out_ground_truth =        16'hdf58;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 25;
	in_valid_i = 1'b1;
	operand1_i =              16'h2a03;
	operand1_i_ascii =        "0.40643310546875";
	operand2_i =              16'h2728;
	operand2_i_ascii =        "0.36181640625";
	result_gt_ascii =         "0.14703369140625";
	out_ground_truth =        16'h1969;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 26;
	in_valid_i = 1'b1;
	operand1_i =              16'h2627;
	operand1_i_ascii =        "0.34613037109375";
	operand2_i =              16'he88f;
	operand2_i_ascii =        "-0.120635986328125";
	result_gt_ascii =         "-0.041748046875";
	out_ground_truth =        16'hf2a8;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 27;
	in_valid_i = 1'b1;
	operand1_i =              16'ha04c;
	operand1_i_ascii =        "-3.962890625";
	operand2_i =              16'h9086;
	operand2_i_ascii =        "-15.4765625";
	result_gt_ascii =         "61.34375";
	out_ground_truth =        16'h77ab;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 28;
	in_valid_i = 1'b1;
	operand1_i =              16'h95c4;
	operand1_i_ascii =        "-10.234375";
	operand2_i =              16'h20c9;
	operand2_i_ascii =        "0.26226806640625";
	result_gt_ascii =         "-2.68408203125";
	out_ground_truth =        16'haa87;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 29;
	in_valid_i = 1'b1;
	operand1_i =              16'h39a8;
	operand1_i_ascii =        "0.8017578125";
	operand2_i =              16'h5357;
	operand2_i_ascii =        "2.41748046875";
	result_gt_ascii =         "1.938232421875";
	out_ground_truth =        16'h4f03;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 30;
	in_valid_i = 1'b1;
	operand1_i =              16'h9381;
	operand1_i_ascii =        "-12.49609375";
	operand2_i =              16'h66d1;
	operand2_i_ascii =        "7.408203125";
	result_gt_ascii =         "-92.625";
	out_ground_truth =        16'h871b;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 31;
	in_valid_i = 1'b1;
	operand1_i =              16'hc3da;
	operand1_i_ascii =        "-0.879638671875";
	operand2_i =              16'he234;
	operand2_i_ascii =        "-0.215576171875";
	result_gt_ascii =         "0.18963623046875";
	out_ground_truth =        16'h1c23;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 32;
	in_valid_i = 1'b0;
	operand1_i =              16'hd428;
	operand1_i_ascii =        "-0.43505859375";
	operand2_i =              16'h39bf;
	operand2_i_ascii =        "0.8045654296875";
	result_gt_ascii =         "-0.35003662109375";
	out_ground_truth =        16'hd999;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 33;
	in_valid_i = 1'b1;
	operand1_i =              16'h08b7;
	operand1_i_ascii =        "0.0184173583984375";
	operand2_i =              16'h29b1;
	operand2_i_ascii =        "0.40142822265625";
	result_gt_ascii =         "0.00739288330078125";
	out_ground_truth =        16'h05c9;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 34;
	in_valid_i = 1'b1;
	operand1_i =              16'h8f3b;
	operand1_i_ascii =        "-19.078125";
	operand2_i =              16'h0bce;
	operand2_i_ascii =        "0.030487060546875";
	result_gt_ascii =         "-0.5816650390625";
	out_ground_truth =        16'hcd63;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 35;
	in_valid_i = 1'b1;
	operand1_i =              16'h90fa;
	operand1_i_ascii =        "-15.0234375";
	operand2_i =              16'hce6d;
	operand2_i_ascii =        "-0.5491943359375";
	result_gt_ascii =         "8.25";
	out_ground_truth =        16'h6840;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 36;
	in_valid_i = 1'b1;
	operand1_i =              16'hdf37;
	operand1_i_ascii =        "-0.26226806640625";
	operand2_i =              16'h7ac6;
	operand2_i_ascii =        "177.5";
	result_gt_ascii =         "-46.5625";
	out_ground_truth =        16'h8a2e;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 37;
	in_valid_i = 1'b1;
	operand1_i =              16'h360e;
	operand1_i_ascii =        "0.689208984375";
	operand2_i =              16'hd0f7;
	operand2_i_ascii =        "-0.48492431640625";
	result_gt_ascii =         "-0.334228515625";
	out_ground_truth =        16'hda9c;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 38;
	in_valid_i = 1'b1;
	operand1_i =              16'h3c1b;
	operand1_i_ascii =        "0.8782958984375";
	operand2_i =              16'h9014;
	operand2_i_ascii =        "-15.921875";
	result_gt_ascii =         "-13.984375";
	out_ground_truth =        16'h9204;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 39;
	in_valid_i = 1'b1;
	operand1_i =              16'h658c;
	operand1_i_ascii =        "6.7734375";
	operand2_i =              16'h07d3;
	operand2_i_ascii =        "0.0149383544921875";
	result_gt_ascii =         "0.1011962890625";
	out_ground_truth =        16'h14f4;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 40;
	in_valid_i = 1'b1;
	operand1_i =              16'h2781;
	operand1_i_ascii =        "0.36724853515625";
	operand2_i =              16'h22c8;
	operand2_i_ascii =        "0.29345703125";
	result_gt_ascii =         "0.107757568359375";
	out_ground_truth =        16'h15cb;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 41;
	in_valid_i = 1'b1;
	operand1_i =              16'h00fa;
	operand1_i_ascii =        "0.000232696533203125";
	operand2_i =              16'hf46c;
	operand2_i_ascii =        "-0.02960205078125";
	result_gt_ascii =         "-6.9141387939453125e-06";
	out_ground_truth =        16'hffd3;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 42;
	in_valid_i = 1'b1;
	operand1_i =              16'hc855;
	operand1_i_ascii =        "-0.7396240234375";
	operand2_i =              16'h5a15;
	operand2_i_ascii =        "3.26025390625";
	result_gt_ascii =         "-2.4111328125";
	out_ground_truth =        16'hacb6;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 43;
	in_valid_i = 1'b1;
	operand1_i =              16'h956b;
	operand1_i_ascii =        "-10.58203125";
	operand2_i =              16'h8d1c;
	operand2_i_ascii =        "-27.5625";
	result_gt_ascii =         "292.0";
	out_ground_truth =        16'h7c24;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 44;
	in_valid_i = 1'b1;
	operand1_i =              16'h6f52;
	operand1_i_ascii =        "15.3203125";
	operand2_i =              16'he882;
	operand2_i_ascii =        "-0.12103271484375";
	result_gt_ascii =         "-1.854248046875";
	out_ground_truth =        16'hb255;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 45;
	in_valid_i = 1'b0;
	operand1_i =              16'hecaa;
	operand1_i_ascii =        "-0.08856201171875";
	operand2_i =              16'hcbaa;
	operand2_i_ascii =        "-0.635498046875";
	result_gt_ascii =         "0.0562744140625";
	out_ground_truth =        16'h0f34;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 46;
	in_valid_i = 1'b1;
	operand1_i =              16'h5dfe;
	operand1_i_ascii =        "3.7490234375";
	operand2_i =              16'h3a51;
	operand2_i_ascii =        "0.8223876953125";
	result_gt_ascii =         "3.0830078125";
	out_ground_truth =        16'h58aa;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 47;
	in_valid_i = 1'b0;
	operand1_i =              16'h2ead;
	operand1_i_ascii =        "0.47930908203125";
	operand2_i =              16'hd0fc;
	operand2_i_ascii =        "-0.484619140625";
	result_gt_ascii =         "-0.2322998046875";
	out_ground_truth =        16'he122;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 48;
	in_valid_i = 1'b1;
	operand1_i =              16'h177a;
	operand1_i_ascii =        "0.12091064453125";
	operand2_i =              16'h7dae;
	operand2_i_ascii =        "860.0";
	result_gt_ascii =         "104.0";
	out_ground_truth =        16'h7940;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 49;
	in_valid_i = 1'b1;
	operand1_i =              16'h03f7;
	operand1_i_ascii =        "0.00383758544921875";
	operand2_i =              16'hbea6;
	operand2_i_ascii =        "-1.08447265625";
	result_gt_ascii =         "-0.00415802001953125";
	out_ground_truth =        16'hfbdf;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 50;
	in_valid_i = 1'b1;
	operand1_i =              16'hdc30;
	operand1_i_ascii =        "-0.3095703125";
	operand2_i =              16'h7058;
	operand2_i_ascii =        "17.375";
	result_gt_ascii =         "-5.37890625";
	out_ground_truth =        16'h9d3e;
	pout_hwdiv_expected =     16'hz;
	
$display("Total tests cases: 50");
op_i = ADD;
op_i_ascii = "ADD";

@(negedge clk_i);
#1.5541;
test_no =                 1;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h9874;
	operand2_i_ascii =        "-7.7734375";
	result_gt_ascii =         "-7.7734375";
	out_ground_truth =        16'h9874;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 2;
	in_valid_i = 1'b1;
	operand1_i =              16'h8000;
	operand1_i_ascii =        "nan";
	operand2_i =              16'h381d;
	operand2_i_ascii =        "0.7535400390625";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 3;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h8000;
	operand2_i_ascii =        "nan";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 4;
	in_valid_i = 1'b0;
	operand1_i =              16'h0db3;
	operand1_i_ascii =        "0.044525146484375";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "0.044525146484375";
	out_ground_truth =        16'h0db3;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 5;
	in_valid_i = 1'b1;
	operand1_i =              16'he409;
	operand1_i_ascii =        "-0.18695068359375";
	operand2_i =              16'h8000;
	operand2_i_ascii =        "nan";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 6;
	in_valid_i = 1'b1;
	operand1_i =              16'h8000;
	operand1_i_ascii =        "nan";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 7;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "0";
	out_ground_truth =        16'h0000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 8;
	in_valid_i = 1'b1;
	operand1_i =              16'he382;
	operand1_i_ascii =        "-0.1951904296875";
	operand2_i =              16'h1c7e;
	operand2_i_ascii =        "0.1951904296875";
	result_gt_ascii =         "0";
	out_ground_truth =        16'h0000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 9;
	in_valid_i = 1'b1;
	operand1_i =              16'h8001;
	operand1_i_ascii =        "-268435456.0";
	operand2_i =              16'hd3b4;
	operand2_i_ascii =        "-0.442138671875";
	result_gt_ascii =         "-268435456.0";
	out_ground_truth =        16'h8001;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 10;
	in_valid_i = 1'b1;
	operand1_i =              16'hf43c;
	operand1_i_ascii =        "-0.03033447265625";
	operand2_i =              16'h702c;
	operand2_i_ascii =        "16.6875";
	result_gt_ascii =         "16.65625";
	out_ground_truth =        16'h702a;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 11;
	in_valid_i = 1'b1;
	operand1_i =              16'hd552;
	operand1_i_ascii =        "-0.4168701171875";
	operand2_i =              16'h698c;
	operand2_i_ascii =        "9.546875";
	result_gt_ascii =         "9.12890625";
	out_ground_truth =        16'h6921;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 12;
	in_valid_i = 1'b1;
	operand1_i =              16'hd60b;
	operand1_i_ascii =        "-0.40557861328125";
	operand2_i =              16'hfc39;
	operand2_i_ascii =        "-0.00347137451171875";
	result_gt_ascii =         "-0.4090576171875";
	out_ground_truth =        16'hd5d2;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 13;
	in_valid_i = 1'b1;
	operand1_i =              16'h679c;
	operand1_i_ascii =        "7.8046875";
	operand2_i =              16'h758e;
	operand2_i_ascii =        "44.4375";
	result_gt_ascii =         "52.25";
	out_ground_truth =        16'h7688;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 14;
	in_valid_i = 1'b1;
	operand1_i =              16'h14c8;
	operand1_i_ascii =        "0.099853515625";
	operand2_i =              16'h7f26;
	operand2_i_ascii =        "6528.0";
	result_gt_ascii =         "6528.0";
	out_ground_truth =        16'h7f26;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 15;
	in_valid_i = 1'b1;
	operand1_i =              16'h4ea8;
	operand1_i_ascii =        "1.916015625";
	operand2_i =              16'hdb6d;
	operand2_i_ascii =        "-0.32147216796875";
	result_gt_ascii =         "1.594482421875";
	out_ground_truth =        16'h4983;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 16;
	in_valid_i = 1'b1;
	operand1_i =              16'h1aad;
	operand1_i_ascii =        "0.16680908203125";
	operand2_i =              16'he85b;
	operand2_i_ascii =        "-0.122222900390625";
	result_gt_ascii =         "0.044586181640625";
	out_ground_truth =        16'h0db5;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 17;
	in_valid_i = 1'b1;
	operand1_i =              16'hc2be;
	operand1_i_ascii =        "-0.914306640625";
	operand2_i =              16'hed84;
	operand2_i_ascii =        "-0.0819091796875";
	result_gt_ascii =         "-0.9962158203125";
	out_ground_truth =        16'hc01f;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 18;
	in_valid_i = 1'b1;
	operand1_i =              16'h69e7;
	operand1_i_ascii =        "9.90234375";
	operand2_i =              16'hd937;
	operand2_i_ascii =        "-0.35601806640625";
	result_gt_ascii =         "9.546875";
	out_ground_truth =        16'h698c;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 19;
	in_valid_i = 1'b1;
	operand1_i =              16'h8599;
	operand1_i_ascii =        "-153.75";
	operand2_i =              16'he957;
	operand2_i_ascii =        "-0.114532470703125";
	result_gt_ascii =         "-153.75";
	out_ground_truth =        16'h8599;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 20;
	in_valid_i = 1'b0;
	operand1_i =              16'h7402;
	operand1_i_ascii =        "32.0625";
	operand2_i =              16'h0407;
	operand2_i_ascii =        "0.00395965576171875";
	result_gt_ascii =         "32.0625";
	out_ground_truth =        16'h7402;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 21;
	in_valid_i = 1'b1;
	operand1_i =              16'h7ef9;
	operand1_i_ascii =        "3984.0";
	operand2_i =              16'h7fe9;
	operand2_i_ascii =        "589824.0";
	result_gt_ascii =         "589824.0";
	out_ground_truth =        16'h7fe9;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 22;
	in_valid_i = 1'b1;
	operand1_i =              16'h6e4d;
	operand1_i_ascii =        "14.30078125";
	operand2_i =              16'hbf00;
	operand2_i_ascii =        "-1.0625";
	result_gt_ascii =         "13.23828125";
	out_ground_truth =        16'h6d3d;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 23;
	in_valid_i = 1'b1;
	operand1_i =              16'h7146;
	operand1_i_ascii =        "21.09375";
	operand2_i =              16'h289e;
	operand2_i_ascii =        "0.3846435546875";
	result_gt_ascii =         "21.484375";
	out_ground_truth =        16'h715f;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 24;
	in_valid_i = 1'b0;
	operand1_i =              16'hd721;
	operand1_i_ascii =        "-0.38861083984375";
	operand2_i =              16'h356e;
	operand2_i_ascii =        "0.669677734375";
	result_gt_ascii =         "0.28106689453125";
	out_ground_truth =        16'h21fd;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 25;
	in_valid_i = 1'b1;
	operand1_i =              16'h2a03;
	operand1_i_ascii =        "0.40643310546875";
	operand2_i =              16'h2728;
	operand2_i_ascii =        "0.36181640625";
	result_gt_ascii =         "0.768310546875";
	out_ground_truth =        16'h3896;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 26;
	in_valid_i = 1'b1;
	operand1_i =              16'h2627;
	operand1_i_ascii =        "0.34613037109375";
	operand2_i =              16'he88f;
	operand2_i_ascii =        "-0.120635986328125";
	result_gt_ascii =         "0.2254638671875";
	out_ground_truth =        16'h1e6e;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 27;
	in_valid_i = 1'b1;
	operand1_i =              16'ha04c;
	operand1_i_ascii =        "-3.962890625";
	operand2_i =              16'h9086;
	operand2_i_ascii =        "-15.4765625";
	result_gt_ascii =         "-19.4375";
	out_ground_truth =        16'h8f24;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 28;
	in_valid_i = 1'b1;
	operand1_i =              16'h95c4;
	operand1_i_ascii =        "-10.234375";
	operand2_i =              16'h20c9;
	operand2_i_ascii =        "0.26226806640625";
	result_gt_ascii =         "-9.97265625";
	out_ground_truth =        16'h9607;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 29;
	in_valid_i = 1'b1;
	operand1_i =              16'h39a8;
	operand1_i_ascii =        "0.8017578125";
	operand2_i =              16'h5357;
	operand2_i_ascii =        "2.41748046875";
	result_gt_ascii =         "3.21923828125";
	out_ground_truth =        16'h59c1;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 30;
	in_valid_i = 1'b1;
	operand1_i =              16'h9381;
	operand1_i_ascii =        "-12.49609375";
	operand2_i =              16'h66d1;
	operand2_i_ascii =        "7.408203125";
	result_gt_ascii =         "-5.087890625";
	out_ground_truth =        16'h9dd3;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 31;
	in_valid_i = 1'b1;
	operand1_i =              16'hc3da;
	operand1_i_ascii =        "-0.879638671875";
	operand2_i =              16'he234;
	operand2_i_ascii =        "-0.215576171875";
	result_gt_ascii =         "-1.09521484375";
	out_ground_truth =        16'hbe7a;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 32;
	in_valid_i = 1'b1;
	operand1_i =              16'hd428;
	operand1_i_ascii =        "-0.43505859375";
	operand2_i =              16'h39bf;
	operand2_i_ascii =        "0.8045654296875";
	result_gt_ascii =         "0.3695068359375";
	out_ground_truth =        16'h27a6;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 33;
	in_valid_i = 1'b1;
	operand1_i =              16'h08b7;
	operand1_i_ascii =        "0.0184173583984375";
	operand2_i =              16'h29b1;
	operand2_i_ascii =        "0.40142822265625";
	result_gt_ascii =         "0.41986083984375";
	out_ground_truth =        16'h2adf;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 34;
	in_valid_i = 1'b1;
	operand1_i =              16'h8f3b;
	operand1_i_ascii =        "-19.078125";
	operand2_i =              16'h0bce;
	operand2_i_ascii =        "0.030487060546875";
	result_gt_ascii =         "-19.046875";
	out_ground_truth =        16'h8f3d;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 35;
	in_valid_i = 1'b1;
	operand1_i =              16'h90fa;
	operand1_i_ascii =        "-15.0234375";
	operand2_i =              16'hce6d;
	operand2_i_ascii =        "-0.5491943359375";
	result_gt_ascii =         "-15.57421875";
	out_ground_truth =        16'h906d;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 36;
	in_valid_i = 1'b1;
	operand1_i =              16'hdf37;
	operand1_i_ascii =        "-0.26226806640625";
	operand2_i =              16'h7ac6;
	operand2_i_ascii =        "177.5";
	result_gt_ascii =         "177.25";
	out_ground_truth =        16'h7ac5;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 37;
	in_valid_i = 1'b1;
	operand1_i =              16'h360e;
	operand1_i_ascii =        "0.689208984375";
	operand2_i =              16'hd0f7;
	operand2_i_ascii =        "-0.48492431640625";
	result_gt_ascii =         "0.20428466796875";
	out_ground_truth =        16'h1d13;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 38;
	in_valid_i = 1'b0;
	operand1_i =              16'h3c1b;
	operand1_i_ascii =        "0.8782958984375";
	operand2_i =              16'h9014;
	operand2_i_ascii =        "-15.921875";
	result_gt_ascii =         "-15.04296875";
	out_ground_truth =        16'h90f5;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 39;
	in_valid_i = 1'b1;
	operand1_i =              16'h658c;
	operand1_i_ascii =        "6.7734375";
	operand2_i =              16'h07d3;
	operand2_i_ascii =        "0.0149383544921875";
	result_gt_ascii =         "6.7890625";
	out_ground_truth =        16'h6594;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 40;
	in_valid_i = 1'b1;
	operand1_i =              16'h2781;
	operand1_i_ascii =        "0.36724853515625";
	operand2_i =              16'h22c8;
	operand2_i_ascii =        "0.29345703125";
	result_gt_ascii =         "0.66064453125";
	out_ground_truth =        16'h3524;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 41;
	in_valid_i = 1'b1;
	operand1_i =              16'h00fa;
	operand1_i_ascii =        "0.000232696533203125";
	operand2_i =              16'hf46c;
	operand2_i_ascii =        "-0.02960205078125";
	result_gt_ascii =         "-0.0293731689453125";
	out_ground_truth =        16'hf47b;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 42;
	in_valid_i = 1'b1;
	operand1_i =              16'hc855;
	operand1_i_ascii =        "-0.7396240234375";
	operand2_i =              16'h5a15;
	operand2_i_ascii =        "3.26025390625";
	result_gt_ascii =         "2.5205078125";
	out_ground_truth =        16'h542a;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 43;
	in_valid_i = 1'b1;
	operand1_i =              16'h956b;
	operand1_i_ascii =        "-10.58203125";
	operand2_i =              16'h8d1c;
	operand2_i_ascii =        "-27.5625";
	result_gt_ascii =         "-38.15625";
	out_ground_truth =        16'h8b3b;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 44;
	in_valid_i = 1'b1;
	operand1_i =              16'h6f52;
	operand1_i_ascii =        "15.3203125";
	operand2_i =              16'he882;
	operand2_i_ascii =        "-0.12103271484375";
	result_gt_ascii =         "15.19921875";
	out_ground_truth =        16'h6f33;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 45;
	in_valid_i = 1'b1;
	operand1_i =              16'hecaa;
	operand1_i_ascii =        "-0.08856201171875";
	operand2_i =              16'hcbaa;
	operand2_i_ascii =        "-0.635498046875";
	result_gt_ascii =         "-0.72412109375";
	out_ground_truth =        16'hc8d4;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 46;
	in_valid_i = 1'b1;
	operand1_i =              16'h5dfe;
	operand1_i_ascii =        "3.7490234375";
	operand2_i =              16'h3a51;
	operand2_i_ascii =        "0.8223876953125";
	result_gt_ascii =         "4.572265625";
	out_ground_truth =        16'h6125;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 47;
	in_valid_i = 1'b1;
	operand1_i =              16'h2ead;
	operand1_i_ascii =        "0.47930908203125";
	operand2_i =              16'hd0fc;
	operand2_i_ascii =        "-0.484619140625";
	result_gt_ascii =         "-0.00531005859375";
	out_ground_truth =        16'hfb48;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 48;
	in_valid_i = 1'b1;
	operand1_i =              16'h177a;
	operand1_i_ascii =        "0.12091064453125";
	operand2_i =              16'h7dae;
	operand2_i_ascii =        "860.0";
	result_gt_ascii =         "860.0";
	out_ground_truth =        16'h7dae;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 49;
	in_valid_i = 1'b1;
	operand1_i =              16'h03f7;
	operand1_i_ascii =        "0.00383758544921875";
	operand2_i =              16'hbea6;
	operand2_i_ascii =        "-1.08447265625";
	result_gt_ascii =         "-1.08056640625";
	out_ground_truth =        16'hbeb6;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 50;
	in_valid_i = 1'b1;
	operand1_i =              16'hdc30;
	operand1_i_ascii =        "-0.3095703125";
	operand2_i =              16'h7058;
	operand2_i_ascii =        "17.375";
	result_gt_ascii =         "17.0625";
	out_ground_truth =        16'h7044;
	pout_hwdiv_expected =     16'hz;
	
$display("Total tests cases: 50");
op_i = SUB;
op_i_ascii = "SUB";

@(negedge clk_i);
#1.5541;
test_no =                 1;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h9874;
	operand2_i_ascii =        "-7.7734375";
	result_gt_ascii =         "7.7734375";
	out_ground_truth =        16'h678c;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 2;
	in_valid_i = 1'b1;
	operand1_i =              16'h8000;
	operand1_i_ascii =        "nan";
	operand2_i =              16'h381d;
	operand2_i_ascii =        "0.7535400390625";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 3;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h8000;
	operand2_i_ascii =        "nan";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 4;
	in_valid_i = 1'b0;
	operand1_i =              16'h0db3;
	operand1_i_ascii =        "0.044525146484375";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "0.044525146484375";
	out_ground_truth =        16'h0db3;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 5;
	in_valid_i = 1'b1;
	operand1_i =              16'he409;
	operand1_i_ascii =        "-0.18695068359375";
	operand2_i =              16'h8000;
	operand2_i_ascii =        "nan";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 6;
	in_valid_i = 1'b1;
	operand1_i =              16'h8000;
	operand1_i_ascii =        "nan";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 7;
	in_valid_i = 1'b0;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "0";
	out_ground_truth =        16'h0000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 8;
	in_valid_i = 1'b1;
	operand1_i =              16'he382;
	operand1_i_ascii =        "-0.1951904296875";
	operand2_i =              16'h1c7e;
	operand2_i_ascii =        "0.1951904296875";
	result_gt_ascii =         "-0.390380859375";
	out_ground_truth =        16'hd704;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 9;
	in_valid_i = 1'b1;
	operand1_i =              16'h8001;
	operand1_i_ascii =        "-268435456.0";
	operand2_i =              16'hd3b4;
	operand2_i_ascii =        "-0.442138671875";
	result_gt_ascii =         "-268435456.0";
	out_ground_truth =        16'h8001;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 10;
	in_valid_i = 1'b1;
	operand1_i =              16'hf43c;
	operand1_i_ascii =        "-0.03033447265625";
	operand2_i =              16'h702c;
	operand2_i_ascii =        "16.6875";
	result_gt_ascii =         "-16.71875";
	out_ground_truth =        16'h8fd2;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 11;
	in_valid_i = 1'b1;
	operand1_i =              16'hd552;
	operand1_i_ascii =        "-0.4168701171875";
	operand2_i =              16'h698c;
	operand2_i_ascii =        "9.546875";
	result_gt_ascii =         "-9.96484375";
	out_ground_truth =        16'h9609;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 12;
	in_valid_i = 1'b1;
	operand1_i =              16'hd60b;
	operand1_i_ascii =        "-0.40557861328125";
	operand2_i =              16'hfc39;
	operand2_i_ascii =        "-0.00347137451171875";
	result_gt_ascii =         "-0.402099609375";
	out_ground_truth =        16'hd644;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 13;
	in_valid_i = 1'b1;
	operand1_i =              16'h679c;
	operand1_i_ascii =        "7.8046875";
	operand2_i =              16'h758e;
	operand2_i_ascii =        "44.4375";
	result_gt_ascii =         "-36.625";
	out_ground_truth =        16'h8b6c;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 14;
	in_valid_i = 1'b1;
	operand1_i =              16'h14c8;
	operand1_i_ascii =        "0.099853515625";
	operand2_i =              16'h7f26;
	operand2_i_ascii =        "6528.0";
	result_gt_ascii =         "-6528.0";
	out_ground_truth =        16'h80da;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 15;
	in_valid_i = 1'b0;
	operand1_i =              16'h4ea8;
	operand1_i_ascii =        "1.916015625";
	operand2_i =              16'hdb6d;
	operand2_i_ascii =        "-0.32147216796875";
	result_gt_ascii =         "2.2373046875";
	out_ground_truth =        16'h51e6;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 16;
	in_valid_i = 1'b1;
	operand1_i =              16'h1aad;
	operand1_i_ascii =        "0.16680908203125";
	operand2_i =              16'he85b;
	operand2_i_ascii =        "-0.122222900390625";
	result_gt_ascii =         "0.2890625";
	out_ground_truth =        16'h2280;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 17;
	in_valid_i = 1'b0;
	operand1_i =              16'hc2be;
	operand1_i_ascii =        "-0.914306640625";
	operand2_i =              16'hed84;
	operand2_i_ascii =        "-0.0819091796875";
	result_gt_ascii =         "-0.8323974609375";
	out_ground_truth =        16'hc55d;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 18;
	in_valid_i = 1'b1;
	operand1_i =              16'h69e7;
	operand1_i_ascii =        "9.90234375";
	operand2_i =              16'hd937;
	operand2_i_ascii =        "-0.35601806640625";
	result_gt_ascii =         "10.2578125";
	out_ground_truth =        16'h6a42;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 19;
	in_valid_i = 1'b1;
	operand1_i =              16'h8599;
	operand1_i_ascii =        "-153.75";
	operand2_i =              16'he957;
	operand2_i_ascii =        "-0.114532470703125";
	result_gt_ascii =         "-153.75";
	out_ground_truth =        16'h8599;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 20;
	in_valid_i = 1'b1;
	operand1_i =              16'h7402;
	operand1_i_ascii =        "32.0625";
	operand2_i =              16'h0407;
	operand2_i_ascii =        "0.00395965576171875";
	result_gt_ascii =         "32.0625";
	out_ground_truth =        16'h7402;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 21;
	in_valid_i = 1'b1;
	operand1_i =              16'h7ef9;
	operand1_i_ascii =        "3984.0";
	operand2_i =              16'h7fe9;
	operand2_i_ascii =        "589824.0";
	result_gt_ascii =         "-589824.0";
	out_ground_truth =        16'h8017;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 22;
	in_valid_i = 1'b1;
	operand1_i =              16'h6e4d;
	operand1_i_ascii =        "14.30078125";
	operand2_i =              16'hbf00;
	operand2_i_ascii =        "-1.0625";
	result_gt_ascii =         "15.36328125";
	out_ground_truth =        16'h6f5d;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 23;
	in_valid_i = 1'b1;
	operand1_i =              16'h7146;
	operand1_i_ascii =        "21.09375";
	operand2_i =              16'h289e;
	operand2_i_ascii =        "0.3846435546875";
	result_gt_ascii =         "20.703125";
	out_ground_truth =        16'h712d;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 24;
	in_valid_i = 1'b1;
	operand1_i =              16'hd721;
	operand1_i_ascii =        "-0.38861083984375";
	operand2_i =              16'h356e;
	operand2_i_ascii =        "0.669677734375";
	result_gt_ascii =         "-1.058349609375";
	out_ground_truth =        16'hbf11;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 25;
	in_valid_i = 1'b1;
	operand1_i =              16'h2a03;
	operand1_i_ascii =        "0.40643310546875";
	operand2_i =              16'h2728;
	operand2_i_ascii =        "0.36181640625";
	result_gt_ascii =         "0.04461669921875";
	out_ground_truth =        16'h0db6;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 26;
	in_valid_i = 1'b1;
	operand1_i =              16'h2627;
	operand1_i_ascii =        "0.34613037109375";
	operand2_i =              16'he88f;
	operand2_i_ascii =        "-0.120635986328125";
	result_gt_ascii =         "0.466796875";
	out_ground_truth =        16'h2de0;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 27;
	in_valid_i = 1'b1;
	operand1_i =              16'ha04c;
	operand1_i_ascii =        "-3.962890625";
	operand2_i =              16'h9086;
	operand2_i_ascii =        "-15.4765625";
	result_gt_ascii =         "11.515625";
	out_ground_truth =        16'h6b84;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 28;
	in_valid_i = 1'b1;
	operand1_i =              16'h95c4;
	operand1_i_ascii =        "-10.234375";
	operand2_i =              16'h20c9;
	operand2_i_ascii =        "0.26226806640625";
	result_gt_ascii =         "-10.49609375";
	out_ground_truth =        16'h9581;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 29;
	in_valid_i = 1'b0;
	operand1_i =              16'h39a8;
	operand1_i_ascii =        "0.8017578125";
	operand2_i =              16'h5357;
	operand2_i_ascii =        "2.41748046875";
	result_gt_ascii =         "-1.61572265625";
	out_ground_truth =        16'hb626;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 30;
	in_valid_i = 1'b1;
	operand1_i =              16'h9381;
	operand1_i_ascii =        "-12.49609375";
	operand2_i =              16'h66d1;
	operand2_i_ascii =        "7.408203125";
	result_gt_ascii =         "-19.90625";
	out_ground_truth =        16'h8f06;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 31;
	in_valid_i = 1'b1;
	operand1_i =              16'hc3da;
	operand1_i_ascii =        "-0.879638671875";
	operand2_i =              16'he234;
	operand2_i_ascii =        "-0.215576171875";
	result_gt_ascii =         "-0.6640625";
	out_ground_truth =        16'hcac0;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 32;
	in_valid_i = 1'b1;
	operand1_i =              16'hd428;
	operand1_i_ascii =        "-0.43505859375";
	operand2_i =              16'h39bf;
	operand2_i_ascii =        "0.8045654296875";
	result_gt_ascii =         "-1.23974609375";
	out_ground_truth =        16'hbc2a;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 33;
	in_valid_i = 1'b0;
	operand1_i =              16'h08b7;
	operand1_i_ascii =        "0.0184173583984375";
	operand2_i =              16'h29b1;
	operand2_i_ascii =        "0.40142822265625";
	result_gt_ascii =         "-0.38299560546875";
	out_ground_truth =        16'hd77d;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 34;
	in_valid_i = 1'b1;
	operand1_i =              16'h8f3b;
	operand1_i_ascii =        "-19.078125";
	operand2_i =              16'h0bce;
	operand2_i_ascii =        "0.030487060546875";
	result_gt_ascii =         "-19.109375";
	out_ground_truth =        16'h8f39;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 35;
	in_valid_i = 1'b1;
	operand1_i =              16'h90fa;
	operand1_i_ascii =        "-15.0234375";
	operand2_i =              16'hce6d;
	operand2_i_ascii =        "-0.5491943359375";
	result_gt_ascii =         "-14.47265625";
	out_ground_truth =        16'h9187;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 36;
	in_valid_i = 1'b1;
	operand1_i =              16'hdf37;
	operand1_i_ascii =        "-0.26226806640625";
	operand2_i =              16'h7ac6;
	operand2_i_ascii =        "177.5";
	result_gt_ascii =         "-177.75";
	out_ground_truth =        16'h8539;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 37;
	in_valid_i = 1'b1;
	operand1_i =              16'h360e;
	operand1_i_ascii =        "0.689208984375";
	operand2_i =              16'hd0f7;
	operand2_i_ascii =        "-0.48492431640625";
	result_gt_ascii =         "1.174072265625";
	out_ground_truth =        16'h42c9;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 38;
	in_valid_i = 1'b1;
	operand1_i =              16'h3c1b;
	operand1_i_ascii =        "0.8782958984375";
	operand2_i =              16'h9014;
	operand2_i_ascii =        "-15.921875";
	result_gt_ascii =         "16.796875";
	out_ground_truth =        16'h7033;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 39;
	in_valid_i = 1'b1;
	operand1_i =              16'h658c;
	operand1_i_ascii =        "6.7734375";
	operand2_i =              16'h07d3;
	operand2_i_ascii =        "0.0149383544921875";
	result_gt_ascii =         "6.7578125";
	out_ground_truth =        16'h6584;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 40;
	in_valid_i = 1'b1;
	operand1_i =              16'h2781;
	operand1_i_ascii =        "0.36724853515625";
	operand2_i =              16'h22c8;
	operand2_i_ascii =        "0.29345703125";
	result_gt_ascii =         "0.07379150390625";
	out_ground_truth =        16'h1172;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 41;
	in_valid_i = 1'b1;
	operand1_i =              16'h00fa;
	operand1_i_ascii =        "0.000232696533203125";
	operand2_i =              16'hf46c;
	operand2_i_ascii =        "-0.02960205078125";
	result_gt_ascii =         "0.0298309326171875";
	out_ground_truth =        16'h0ba3;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 42;
	in_valid_i = 1'b1;
	operand1_i =              16'hc855;
	operand1_i_ascii =        "-0.7396240234375";
	operand2_i =              16'h5a15;
	operand2_i_ascii =        "3.26025390625";
	result_gt_ascii =         "-4.0";
	out_ground_truth =        16'ha000;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 43;
	in_valid_i = 1'b1;
	operand1_i =              16'h956b;
	operand1_i_ascii =        "-10.58203125";
	operand2_i =              16'h8d1c;
	operand2_i_ascii =        "-27.5625";
	result_gt_ascii =         "16.984375";
	out_ground_truth =        16'h703f;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 44;
	in_valid_i = 1'b1;
	operand1_i =              16'h6f52;
	operand1_i_ascii =        "15.3203125";
	operand2_i =              16'he882;
	operand2_i_ascii =        "-0.12103271484375";
	result_gt_ascii =         "15.44140625";
	out_ground_truth =        16'h6f71;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 45;
	in_valid_i = 1'b1;
	operand1_i =              16'hecaa;
	operand1_i_ascii =        "-0.08856201171875";
	operand2_i =              16'hcbaa;
	operand2_i_ascii =        "-0.635498046875";
	result_gt_ascii =         "0.546875";
	out_ground_truth =        16'h3180;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 46;
	in_valid_i = 1'b0;
	operand1_i =              16'h5dfe;
	operand1_i_ascii =        "3.7490234375";
	operand2_i =              16'h3a51;
	operand2_i_ascii =        "0.8223876953125";
	result_gt_ascii =         "2.9267578125";
	out_ground_truth =        16'h576a;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 47;
	in_valid_i = 1'b1;
	operand1_i =              16'h2ead;
	operand1_i_ascii =        "0.47930908203125";
	operand2_i =              16'hd0fc;
	operand2_i_ascii =        "-0.484619140625";
	result_gt_ascii =         "0.9638671875";
	out_ground_truth =        16'h3ed8;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 48;
	in_valid_i = 1'b1;
	operand1_i =              16'h177a;
	operand1_i_ascii =        "0.12091064453125";
	operand2_i =              16'h7dae;
	operand2_i_ascii =        "860.0";
	result_gt_ascii =         "-860.0";
	out_ground_truth =        16'h8252;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 49;
	in_valid_i = 1'b1;
	operand1_i =              16'h03f7;
	operand1_i_ascii =        "0.00383758544921875";
	operand2_i =              16'hbea6;
	operand2_i_ascii =        "-1.08447265625";
	result_gt_ascii =         "1.08837890625";
	out_ground_truth =        16'h416a;
	pout_hwdiv_expected =     16'hz;
	
@(negedge clk_i);
#1.5541;
test_no =                 50;
	in_valid_i = 1'b1;
	operand1_i =              16'hdc30;
	operand1_i_ascii =        "-0.3095703125";
	operand2_i =              16'h7058;
	operand2_i_ascii =        "17.375";
	result_gt_ascii =         "-17.6875";
	out_ground_truth =        16'h8f94;
	pout_hwdiv_expected =     16'hz;
	
$display("Total tests cases: 50");
op_i = DIV;
op_i_ascii = "DIV";

@(negedge clk_i);
#1.5541;
test_no =                 1;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h9874;
	operand2_i_ascii =        "-7.7734375";
	result_gt_ascii =         "0";
	out_ground_truth =        16'h0000;
	pout_hwdiv_expected =     16'h0000;
	
@(negedge clk_i);
#1.5541;
test_no =                 2;
	in_valid_i = 1'b1;
	operand1_i =              16'h8000;
	operand1_i_ascii =        "nan";
	operand2_i =              16'h381d;
	operand2_i_ascii =        "0.7535400390625";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'h8000;
	
@(negedge clk_i);
#1.5541;
test_no =                 3;
	in_valid_i = 1'b0;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h8000;
	operand2_i_ascii =        "nan";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'h8000;
	
@(negedge clk_i);
#1.5541;
test_no =                 4;
	in_valid_i = 1'b0;
	operand1_i =              16'h0db3;
	operand1_i_ascii =        "0.044525146484375";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'h8000;
	
@(negedge clk_i);
#1.5541;
test_no =                 5;
	in_valid_i = 1'b1;
	operand1_i =              16'he409;
	operand1_i_ascii =        "-0.18695068359375";
	operand2_i =              16'h8000;
	operand2_i_ascii =        "nan";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'h8000;
	
@(negedge clk_i);
#1.5541;
test_no =                 6;
	in_valid_i = 1'b1;
	operand1_i =              16'h8000;
	operand1_i_ascii =        "nan";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'h8000;
	
@(negedge clk_i);
#1.5541;
test_no =                 7;
	in_valid_i = 1'b1;
	operand1_i =              16'h0000;
	operand1_i_ascii =        "0";
	operand2_i =              16'h0000;
	operand2_i_ascii =        "0";
	result_gt_ascii =         "nan";
	out_ground_truth =        16'h8000;
	pout_hwdiv_expected =     16'h8000;
	
@(negedge clk_i);
#1.5541;
test_no =                 8;
	in_valid_i = 1'b0;
	operand1_i =              16'he382;
	operand1_i_ascii =        "-0.1951904296875";
	operand2_i =              16'h1c7e;
	operand2_i_ascii =        "0.1951904296875";
	result_gt_ascii =         "-1.0";
	out_ground_truth =        16'hc000;
	pout_hwdiv_expected =     16'hc000;
	
@(negedge clk_i);
#1.5541;
test_no =                 9;
	in_valid_i = 1'b1;
	operand1_i =              16'h8001;
	operand1_i_ascii =        "-268435456.0";
	operand2_i =              16'hd3b4;
	operand2_i_ascii =        "-0.442138671875";
	result_gt_ascii =         "268435456.0";
	out_ground_truth =        16'h7fff;
	pout_hwdiv_expected =     16'h7fff;
	
@(negedge clk_i);
#1.5541;
test_no =                 10;
	in_valid_i = 1'b1;
	operand1_i =              16'hf43c;
	operand1_i_ascii =        "-0.03033447265625";
	operand2_i =              16'h702c;
	operand2_i_ascii =        "16.6875";
	result_gt_ascii =         "-0.001819610595703125";
	out_ground_truth =        16'hfd23;
	pout_hwdiv_expected =     16'hfd23;
	
@(negedge clk_i);
#1.5541;
test_no =                 11;
	in_valid_i = 1'b1;
	operand1_i =              16'hd552;
	operand1_i_ascii =        "-0.4168701171875";
	operand2_i =              16'h698c;
	operand2_i_ascii =        "9.546875";
	result_gt_ascii =         "-0.043670654296875";
	out_ground_truth =        16'hf269;
	pout_hwdiv_expected =     16'hf269;
	
@(negedge clk_i);
#1.5541;
test_no =                 12;
	in_valid_i = 1'b1;
	operand1_i =              16'hd60b;
	operand1_i_ascii =        "-0.40557861328125";
	operand2_i =              16'hfc39;
	operand2_i_ascii =        "-0.00347137451171875";
	result_gt_ascii =         "116.875";
	out_ground_truth =        16'h79a7;
	pout_hwdiv_expected =     16'h79a7;
	
@(negedge clk_i);
#1.5541;
test_no =                 13;
	in_valid_i = 1'b1;
	operand1_i =              16'h679c;
	operand1_i_ascii =        "7.8046875";
	operand2_i =              16'h758e;
	operand2_i_ascii =        "44.4375";
	result_gt_ascii =         "0.1756591796875";
	out_ground_truth =        16'h1b3e;
	pout_hwdiv_expected =     16'h1b3e;
	
@(negedge clk_i);
#1.5541;
test_no =                 14;
	in_valid_i = 1'b1;
	operand1_i =              16'h14c8;
	operand1_i_ascii =        "0.099853515625";
	operand2_i =              16'h7f26;
	operand2_i_ascii =        "6528.0";
	result_gt_ascii =         "1.52587890625e-05";
	out_ground_truth =        16'h0040;
	pout_hwdiv_expected =     16'h0040;
	
@(negedge clk_i);
#1.5541;
test_no =                 15;
	in_valid_i = 1'b1;
	operand1_i =              16'h4ea8;
	operand1_i_ascii =        "1.916015625";
	operand2_i =              16'hdb6d;
	operand2_i_ascii =        "-0.32147216796875";
	result_gt_ascii =         "-5.9609375";
	out_ground_truth =        16'h9c14;
	pout_hwdiv_expected =     16'h9c14;
	
@(negedge clk_i);
#1.5541;
test_no =                 16;
	in_valid_i = 1'b1;
	operand1_i =              16'h1aad;
	operand1_i_ascii =        "0.16680908203125";
	operand2_i =              16'he85b;
	operand2_i_ascii =        "-0.122222900390625";
	result_gt_ascii =         "-1.36474609375";
	out_ground_truth =        16'hba2a;
	pout_hwdiv_expected =     16'hba2a;
	
@(negedge clk_i);
#1.5541;
test_no =                 17;
	in_valid_i = 1'b1;
	operand1_i =              16'hc2be;
	operand1_i_ascii =        "-0.914306640625";
	operand2_i =              16'hed84;
	operand2_i_ascii =        "-0.0819091796875";
	result_gt_ascii =         "11.1640625";
	out_ground_truth =        16'h6b2a;
	pout_hwdiv_expected =     16'h6b2a;
	
@(negedge clk_i);
#1.5541;
test_no =                 18;
	in_valid_i = 1'b1;
	operand1_i =              16'h69e7;
	operand1_i_ascii =        "9.90234375";
	operand2_i =              16'hd937;
	operand2_i_ascii =        "-0.35601806640625";
	result_gt_ascii =         "-27.8125";
	out_ground_truth =        16'h8d0c;
	pout_hwdiv_expected =     16'h8d0c;
	
@(negedge clk_i);
#1.5541;
test_no =                 19;
	in_valid_i = 1'b1;
	operand1_i =              16'h8599;
	operand1_i_ascii =        "-153.75";
	operand2_i =              16'he957;
	operand2_i_ascii =        "-0.114532470703125";
	result_gt_ascii =         "1344.0";
	out_ground_truth =        16'h7e28;
	pout_hwdiv_expected =     16'h7e28;
	
@(negedge clk_i);
#1.5541;
test_no =                 20;
	in_valid_i = 1'b1;
	operand1_i =              16'h7402;
	operand1_i_ascii =        "32.0625";
	operand2_i =              16'h0407;
	operand2_i_ascii =        "0.00395965576171875";
	result_gt_ascii =         "8128.0";
	out_ground_truth =        16'h7f3f;
	pout_hwdiv_expected =     16'h7f3f;
	
@(negedge clk_i);
#1.5541;
test_no =                 21;
	in_valid_i = 1'b1;
	operand1_i =              16'h7ef9;
	operand1_i_ascii =        "3984.0";
	operand2_i =              16'h7fe9;
	operand2_i_ascii =        "589824.0";
	result_gt_ascii =         "0.00675201416015625";
	out_ground_truth =        16'h0575;
	pout_hwdiv_expected =     16'h0575;
	
@(negedge clk_i);
#1.5541;
test_no =                 22;
	in_valid_i = 1'b1;
	operand1_i =              16'h6e4d;
	operand1_i_ascii =        "14.30078125";
	operand2_i =              16'hbf00;
	operand2_i_ascii =        "-1.0625";
	result_gt_ascii =         "-13.4609375";
	out_ground_truth =        16'h928a;
	pout_hwdiv_expected =     16'h928a;
	
@(negedge clk_i);
#1.5541;
test_no =                 23;
	in_valid_i = 1'b0;
	operand1_i =              16'h7146;
	operand1_i_ascii =        "21.09375";
	operand2_i =              16'h289e;
	operand2_i_ascii =        "0.3846435546875";
	result_gt_ascii =         "54.84375";
	out_ground_truth =        16'h76db;
	pout_hwdiv_expected =     16'h76db;
	
@(negedge clk_i);
#1.5541;
test_no =                 24;
	in_valid_i = 1'b1;
	operand1_i =              16'hd721;
	operand1_i_ascii =        "-0.38861083984375";
	operand2_i =              16'h356e;
	operand2_i_ascii =        "0.669677734375";
	result_gt_ascii =         "-0.580322265625";
	out_ground_truth =        16'hcd6e;
	pout_hwdiv_expected =     16'hcd6e;
	
@(negedge clk_i);
#1.5541;
test_no =                 25;
	in_valid_i = 1'b1;
	operand1_i =              16'h2a03;
	operand1_i_ascii =        "0.40643310546875";
	operand2_i =              16'h2728;
	operand2_i_ascii =        "0.36181640625";
	result_gt_ascii =         "1.123291015625";
	out_ground_truth =        16'h41f9;
	pout_hwdiv_expected =     16'h41f9;
	
@(negedge clk_i);
#1.5541;
test_no =                 26;
	in_valid_i = 1'b1;
	operand1_i =              16'h2627;
	operand1_i_ascii =        "0.34613037109375";
	operand2_i =              16'he88f;
	operand2_i_ascii =        "-0.120635986328125";
	result_gt_ascii =         "-2.869140625";
	out_ground_truth =        16'ha90c;
	pout_hwdiv_expected =     16'ha90c;
	
@(negedge clk_i);
#1.5541;
test_no =                 27;
	in_valid_i = 1'b1;
	operand1_i =              16'ha04c;
	operand1_i_ascii =        "-3.962890625";
	operand2_i =              16'h9086;
	operand2_i_ascii =        "-15.4765625";
	result_gt_ascii =         "0.25604248046875";
	out_ground_truth =        16'h2063;
	pout_hwdiv_expected =     16'h2063;
	
@(negedge clk_i);
#1.5541;
test_no =                 28;
	in_valid_i = 1'b1;
	operand1_i =              16'h95c4;
	operand1_i_ascii =        "-10.234375";
	operand2_i =              16'h20c9;
	operand2_i_ascii =        "0.26226806640625";
	result_gt_ascii =         "-39.03125";
	out_ground_truth =        16'h8b1f;
	pout_hwdiv_expected =     16'h8b1f;
	
@(negedge clk_i);
#1.5541;
test_no =                 29;
	in_valid_i = 1'b0;
	operand1_i =              16'h39a8;
	operand1_i_ascii =        "0.8017578125";
	operand2_i =              16'h5357;
	operand2_i_ascii =        "2.41748046875";
	result_gt_ascii =         "0.3316650390625";
	out_ground_truth =        16'h253a;
	pout_hwdiv_expected =     16'h253a;
	
@(negedge clk_i);
#1.5541;
test_no =                 30;
	in_valid_i = 1'b1;
	operand1_i =              16'h9381;
	operand1_i_ascii =        "-12.49609375";
	operand2_i =              16'h66d1;
	operand2_i_ascii =        "7.408203125";
	result_gt_ascii =         "-1.686767578125";
	out_ground_truth =        16'hb503;
	pout_hwdiv_expected =     16'hb503;
	
@(negedge clk_i);
#1.5541;
test_no =                 31;
	in_valid_i = 1'b1;
	operand1_i =              16'hc3da;
	operand1_i_ascii =        "-0.879638671875";
	operand2_i =              16'he234;
	operand2_i_ascii =        "-0.215576171875";
	result_gt_ascii =         "4.080078125";
	out_ground_truth =        16'h6029;
	pout_hwdiv_expected =     16'h6029;
	
@(negedge clk_i);
#1.5541;
test_no =                 32;
	in_valid_i = 1'b1;
	operand1_i =              16'hd428;
	operand1_i_ascii =        "-0.43505859375";
	operand2_i =              16'h39bf;
	operand2_i_ascii =        "0.8045654296875";
	result_gt_ascii =         "-0.540771484375";
	out_ground_truth =        16'hceb2;
	pout_hwdiv_expected =     16'hceb2;
	
@(negedge clk_i);
#1.5541;
test_no =                 33;
	in_valid_i = 1'b1;
	operand1_i =              16'h08b7;
	operand1_i_ascii =        "0.0184173583984375";
	operand2_i =              16'h29b1;
	operand2_i_ascii =        "0.40142822265625";
	result_gt_ascii =         "0.045867919921875";
	out_ground_truth =        16'h0ddf;
	pout_hwdiv_expected =     16'h0ddf;
	
@(negedge clk_i);
#1.5541;
test_no =                 34;
	in_valid_i = 1'b1;
	operand1_i =              16'h8f3b;
	operand1_i_ascii =        "-19.078125";
	operand2_i =              16'h0bce;
	operand2_i_ascii =        "0.030487060546875";
	result_gt_ascii =         "-626.0";
	out_ground_truth =        16'h82c7;
	pout_hwdiv_expected =     16'h82c7;
	
@(negedge clk_i);
#1.5541;
test_no =                 35;
	in_valid_i = 1'b1;
	operand1_i =              16'h90fa;
	operand1_i_ascii =        "-15.0234375";
	operand2_i =              16'hce6d;
	operand2_i_ascii =        "-0.5491943359375";
	result_gt_ascii =         "27.359375";
	out_ground_truth =        16'h72d7;
	pout_hwdiv_expected =     16'h72d7;
	
@(negedge clk_i);
#1.5541;
test_no =                 36;
	in_valid_i = 1'b1;
	operand1_i =              16'hdf37;
	operand1_i_ascii =        "-0.26226806640625";
	operand2_i =              16'h7ac6;
	operand2_i_ascii =        "177.5";
	result_gt_ascii =         "-0.001476287841796875";
	out_ground_truth =        16'hfd7d;
	pout_hwdiv_expected =     16'hfd7d;
	
@(negedge clk_i);
#1.5541;
test_no =                 37;
	in_valid_i = 1'b1;
	operand1_i =              16'h360e;
	operand1_i_ascii =        "0.689208984375";
	operand2_i =              16'hd0f7;
	operand2_i_ascii =        "-0.48492431640625";
	result_gt_ascii =         "-1.42138671875";
	out_ground_truth =        16'hb942;
	pout_hwdiv_expected =     16'hb942;
	
@(negedge clk_i);
#1.5541;
test_no =                 38;
	in_valid_i = 1'b1;
	operand1_i =              16'h3c1b;
	operand1_i_ascii =        "0.8782958984375";
	operand2_i =              16'h9014;
	operand2_i_ascii =        "-15.921875";
	result_gt_ascii =         "-0.05517578125";
	out_ground_truth =        16'hf0f0;
	pout_hwdiv_expected =     16'hf0f0;
	
@(negedge clk_i);
#1.5541;
test_no =                 39;
	in_valid_i = 1'b1;
	operand1_i =              16'h658c;
	operand1_i_ascii =        "6.7734375";
	operand2_i =              16'h07d3;
	operand2_i_ascii =        "0.0149383544921875";
	result_gt_ascii =         "453.0";
	out_ground_truth =        16'h7cc5;
	pout_hwdiv_expected =     16'h7cc5;
	
@(negedge clk_i);
#1.5541;
test_no =                 40;
	in_valid_i = 1'b0;
	operand1_i =              16'h2781;
	operand1_i_ascii =        "0.36724853515625";
	operand2_i =              16'h22c8;
	operand2_i_ascii =        "0.29345703125";
	result_gt_ascii =         "1.25146484375";
	out_ground_truth =        16'h4406;
	pout_hwdiv_expected =     16'h4406;
	
@(negedge clk_i);
#1.5541;
test_no =                 41;
	in_valid_i = 1'b1;
	operand1_i =              16'h00fa;
	operand1_i_ascii =        "0.000232696533203125";
	operand2_i =              16'hf46c;
	operand2_i_ascii =        "-0.02960205078125";
	result_gt_ascii =         "-0.0078582763671875";
	out_ground_truth =        16'hf9fd;
	pout_hwdiv_expected =     16'hf9fd;
	
@(negedge clk_i);
#1.5541;
test_no =                 42;
	in_valid_i = 1'b1;
	operand1_i =              16'hc855;
	operand1_i_ascii =        "-0.7396240234375";
	operand2_i =              16'h5a15;
	operand2_i_ascii =        "3.26025390625";
	result_gt_ascii =         "-0.22686767578125";
	out_ground_truth =        16'he17b;
	pout_hwdiv_expected =     16'he17b;
	
@(negedge clk_i);
#1.5541;
test_no =                 43;
	in_valid_i = 1'b1;
	operand1_i =              16'h956b;
	operand1_i_ascii =        "-10.58203125";
	operand2_i =              16'h8d1c;
	operand2_i_ascii =        "-27.5625";
	result_gt_ascii =         "0.3839111328125";
	out_ground_truth =        16'h2892;
	pout_hwdiv_expected =     16'h2892;
	
@(negedge clk_i);
#1.5541;
test_no =                 44;
	in_valid_i = 1'b1;
	operand1_i =              16'h6f52;
	operand1_i_ascii =        "15.3203125";
	operand2_i =              16'he882;
	operand2_i_ascii =        "-0.12103271484375";
	result_gt_ascii =         "-126.625";
	out_ground_truth =        16'h860b;
	pout_hwdiv_expected =     16'h860b;
	
@(negedge clk_i);
#1.5541;
test_no =                 45;
	in_valid_i = 1'b1;
	operand1_i =              16'hecaa;
	operand1_i_ascii =        "-0.08856201171875";
	operand2_i =              16'hcbaa;
	operand2_i_ascii =        "-0.635498046875";
	result_gt_ascii =         "0.13934326171875";
	out_ground_truth =        16'h18eb;
	pout_hwdiv_expected =     16'h18eb;
	
@(negedge clk_i);
#1.5541;
test_no =                 46;
	in_valid_i = 1'b1;
	operand1_i =              16'h5dfe;
	operand1_i_ascii =        "3.7490234375";
	operand2_i =              16'h3a51;
	operand2_i_ascii =        "0.8223876953125";
	result_gt_ascii =         "4.55859375";
	out_ground_truth =        16'h611e;
	pout_hwdiv_expected =     16'h611e;
	
@(negedge clk_i);
#1.5541;
test_no =                 47;
	in_valid_i = 1'b1;
	operand1_i =              16'h2ead;
	operand1_i_ascii =        "0.47930908203125";
	operand2_i =              16'hd0fc;
	operand2_i_ascii =        "-0.484619140625";
	result_gt_ascii =         "-0.989013671875";
	out_ground_truth =        16'hc05a;
	pout_hwdiv_expected =     16'hc05a;
	
@(negedge clk_i);
#1.5541;
test_no =                 48;
	in_valid_i = 1'b1;
	operand1_i =              16'h177a;
	operand1_i_ascii =        "0.12091064453125";
	operand2_i =              16'h7dae;
	operand2_i_ascii =        "860.0";
	result_gt_ascii =         "0.000141143798828125";
	out_ground_truth =        16'h00ca;
	pout_hwdiv_expected =     16'h00ca;
	
@(negedge clk_i);
#1.5541;
test_no =                 49;
	in_valid_i = 1'b1;
	operand1_i =              16'h03f7;
	operand1_i_ascii =        "0.00383758544921875";
	operand2_i =              16'hbea6;
	operand2_i_ascii =        "-1.08447265625";
	result_gt_ascii =         "-0.0035400390625";
	out_ground_truth =        16'hfc30;
	pout_hwdiv_expected =     16'hfc30;
	
@(negedge clk_i);
#1.5541;
test_no =                 50;
	in_valid_i = 1'b1;
	operand1_i =              16'hdc30;
	operand1_i_ascii =        "-0.3095703125";
	operand2_i =              16'h7058;
	operand2_i_ascii =        "17.375";
	result_gt_ascii =         "-0.017822265625";
	out_ground_truth =        16'hf770;
	pout_hwdiv_expected =     16'hf770;
	
$display("Total tests cases: 50");
@(negedge clk_i);
    in_valid_i = 1'b0;
    for (int i=0; i<4; i++) begin
      @(negedge clk_i);
    end
    
    $finish;
  end

endmodule: tb_ppu

