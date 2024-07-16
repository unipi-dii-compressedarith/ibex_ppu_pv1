// Compiled by morty-0.9.0 / 2024-06-11 11:57:03.421738 +00:00:00

/// Contains all the parameters and functions used in the core

/* verilator lint_off DECLFILENAME */
/* verilator lint_off UNUSEDPARAM */
/* verilator lint_off VARHIDDEN */
package ppu_pkg;

/// Posit size 
parameter N = 16;


/// Posit exponent width
parameter ES = 1;




localparam OP_BITS = $clog2(7);
typedef enum logic [OP_BITS-1:0] {
  ADD,
  SUB,
  MUL,
  DIV,
  FMADD_S, // FMADD start: accumulator is initialized
  FMADD_C, // FMADD continue: accumulator maintains its value
  F2P,
  P2F
} operation_e;


typedef struct packed {
  logic [N-1:0] bits;
} posit_t;

typedef struct packed {
  posit_t posit;
  logic   special_tag;
} posit_special_t;


/// S := ceil(log2(N))
parameter S = $clog2(N);

/// Total exponent bits
parameter TE_BITS = (ES + 1) + (S + 1);

/// Regime length bits
parameter REG_LEN_BITS = S + 1;

/// Mantissa length bits
parameter MANT_LEN_BITS = S + 1;

/// K, no of bits
parameter K_BITS = S + 2; // prev. S + 1 (leads to bug when `te` too large)

parameter FRAC_SIZE = N - 1;

// mant (mantissa) and frac (fraction) are
// not the same thing. mant is a Fx<1,MANT_SIZE>.
// frac is a Fx<0, MANT_SIZE-1>
parameter MANT_SIZE = N - 2;


/////////////////////////////////////////////////////////////////////////////
/// Exponent
typedef logic /*signed*/ [TE_BITS-1:0]  exponent_t;
/// WORD
typedef logic [32-1:0]                word_t;
/////////////////////////////////////////////////////////////////////////////


/// FMA accumulator
typedef logic [64-1:0] accumulator_t;



// Operation input FIR type.
typedef struct packed {
  logic                 sign;
  exponent_t            total_exponent;
  logic [MANT_SIZE-1:0] mant;
} fir_t;


parameter MS = MANT_SIZE;  // alias

parameter MAX_TE_DIFF = MS;  // not really, but it works anyway.
parameter MTD = MAX_TE_DIFF;  // alias


parameter RECIPROCATE_MANT_SIZE = 2 * MANT_SIZE;
parameter RMS = RECIPROCATE_MANT_SIZE;  // alias

/****************************************/
parameter MANT_MUL_RESULT_SIZE = 2 * MS;
parameter MANT_ADD_RESULT_SIZE = MS + MTD + 1;
parameter MANT_SUB_RESULT_SIZE = MS + MTD;
parameter MANT_DIV_RESULT_SIZE = MS + RMS;
/****************************************/
parameter FRAC_FULL_SIZE = MANT_DIV_RESULT_SIZE - 2; // this is the largest among all the operation, most likely.

/// Fir type (output of `ops` stage. Fraction is unrounded.)
typedef struct packed {
  logic                       sign;
  exponent_t                  total_exponent;
  logic [FRAC_FULL_SIZE-1:0]  frac;
} long_fir_t; // prev. FIR_TOTAL_SIZE

/// Ops (posit operations) output "metadata" type (?)
typedef struct packed {
  long_fir_t  long_fir;
  logic       frac_truncated;
} ops_out_meta_t;

/// Zero
parameter ZERO = {16{1'b0}};
/// Not A Real
parameter NAR = {1'b1, {16 - 1{1'b0}}};















/*
Fixed point equivalent values of the rational numbers
1.466, 1.0012, 2.0 expressed on a range of different bits.

to visualize what i mean try:

>>> import fixed2float as f2f
>>> a = f2f.Fx(3148211028, 1, 32) # e.g.: fx_1_466___N32
>>> print(a, a.eval())


This file exists because SV doesn't support proper conditional compilation.
*/

// Fixedpoint format of 1.4567844114901045
parameter fx_1_466___N4 = 2'd3; // Fx<1, 2>
parameter fx_1_466___N5 = 3'd6; // Fx<1, 3>
parameter fx_1_466___N6 = 4'd12; // Fx<1, 4>
parameter fx_1_466___N7 = 5'd23; // Fx<1, 5>
parameter fx_1_466___N8 = 6'd47; // Fx<1, 6>
parameter fx_1_466___N9 = 7'd93; // Fx<1, 7>
parameter fx_1_466___N10 = 8'd186; // Fx<1, 8>
parameter fx_1_466___N11 = 9'd373; // Fx<1, 9>
parameter fx_1_466___N12 = 10'd746; // Fx<1, 10>
parameter fx_1_466___N13 = 11'd1492; // Fx<1, 11>
parameter fx_1_466___N14 = 12'd2983; // Fx<1, 12>
parameter fx_1_466___N15 = 13'd5967; // Fx<1, 13>
parameter fx_1_466___N16 = 14'd11934; // Fx<1, 14>
parameter fx_1_466___N17 = 15'd23868; // Fx<1, 15>
parameter fx_1_466___N18 = 16'd47736; // Fx<1, 16>
parameter fx_1_466___N19 = 17'd95472; // Fx<1, 17>
parameter fx_1_466___N20 = 18'd190944; // Fx<1, 18>
parameter fx_1_466___N21 = 19'd381887; // Fx<1, 19>
parameter fx_1_466___N22 = 20'd763775; // Fx<1, 20>
parameter fx_1_466___N23 = 21'd1527549; // Fx<1, 21>
parameter fx_1_466___N24 = 22'd3055098; // Fx<1, 22>
parameter fx_1_466___N25 = 23'd6110197; // Fx<1, 23>
parameter fx_1_466___N26 = 24'd12220393; // Fx<1, 24>
parameter fx_1_466___N27 = 25'd24440787; // Fx<1, 25>
parameter fx_1_466___N28 = 26'd48881573; // Fx<1, 26>
parameter fx_1_466___N29 = 27'd97763147; // Fx<1, 27>
parameter fx_1_466___N30 = 28'd195526294; // Fx<1, 28>
parameter fx_1_466___N31 = 29'd391052588; // Fx<1, 29>
parameter fx_1_466___N32 = 30'd782105176; // Fx<1, 30>

// Fixedpoint format of 1.0009290026616422
parameter fx_1_0012___N4 = 3'd4; // Fx<1, 3>
parameter fx_1_0012___N5 = 5'd16; // Fx<1, 5>
parameter fx_1_0012___N6 = 7'd64; // Fx<1, 7>
parameter fx_1_0012___N7 = 9'd256; // Fx<1, 9>
parameter fx_1_0012___N8 = 11'd1025; // Fx<1, 11>
parameter fx_1_0012___N9 = 13'd4100; // Fx<1, 13>
parameter fx_1_0012___N10 = 15'd16399; // Fx<1, 15>
parameter fx_1_0012___N11 = 17'd65597; // Fx<1, 17>
parameter fx_1_0012___N12 = 19'd262388; // Fx<1, 19>
parameter fx_1_0012___N13 = 21'd1049550; // Fx<1, 21>
parameter fx_1_0012___N14 = 23'd4198201; // Fx<1, 23>
parameter fx_1_0012___N15 = 25'd16792802; // Fx<1, 25>
parameter fx_1_0012___N16 = 27'd67171208; // Fx<1, 27>
parameter fx_1_0012___N17 = 29'd268684833; // Fx<1, 29>
parameter fx_1_0012___N18 = 31'd1074739333; // Fx<1, 31>
parameter fx_1_0012___N19 = 33'd4298957332; // Fx<1, 33>
parameter fx_1_0012___N20 = 35'd17195829328; // Fx<1, 35>
parameter fx_1_0012___N21 = 37'd68783317313; // Fx<1, 37>
parameter fx_1_0012___N22 = 39'd275133269251; // Fx<1, 39>
parameter fx_1_0012___N23 = 41'd1100533077005; // Fx<1, 41>
parameter fx_1_0012___N24 = 43'd4402132308019; // Fx<1, 43>
parameter fx_1_0012___N25 = 45'd17608529232075; // Fx<1, 45>
parameter fx_1_0012___N26 = 47'd70434116928301; // Fx<1, 47>
parameter fx_1_0012___N27 = 49'd281736467713206; // Fx<1, 49>
parameter fx_1_0012___N28 = 51'd1126945870852824; // Fx<1, 51>
parameter fx_1_0012___N29 = 53'd4507783483411295; // Fx<1, 53>
parameter fx_1_0012___N30 = 55'd18031133933645177; // Fx<1, 55>
parameter fx_1_0012___N31 = 57'd72124535734580705; // Fx<1, 57>
parameter fx_1_0012___N32 = 59'd288498142938322817; // Fx<1, 59>

// Fixedpoint format of 2.0
parameter fx_2___N4 = 4'd8; // Fx<2, 4>
parameter fx_2___N5 = 6'd32; // Fx<2, 6>
parameter fx_2___N6 = 8'd128; // Fx<2, 8>
parameter fx_2___N7 = 10'd512; // Fx<2, 10>
parameter fx_2___N8 = 12'd2048; // Fx<2, 12>
parameter fx_2___N9 = 14'd8192; // Fx<2, 14>
parameter fx_2___N10 = 16'd32768; // Fx<2, 16>
parameter fx_2___N11 = 18'd131072; // Fx<2, 18>
parameter fx_2___N12 = 20'd524288; // Fx<2, 20>
parameter fx_2___N13 = 22'd2097152; // Fx<2, 22>
parameter fx_2___N14 = 24'd8388608; // Fx<2, 24>
parameter fx_2___N15 = 26'd33554432; // Fx<2, 26>
parameter fx_2___N16 = 28'd134217728; // Fx<2, 28>
parameter fx_2___N17 = 30'd536870912; // Fx<2, 30>
parameter fx_2___N18 = 32'd2147483648; // Fx<2, 32>
parameter fx_2___N19 = 34'd8589934592; // Fx<2, 34>
parameter fx_2___N20 = 36'd34359738368; // Fx<2, 36>
parameter fx_2___N21 = 38'd137438953472; // Fx<2, 38>
parameter fx_2___N22 = 40'd549755813888; // Fx<2, 40>
parameter fx_2___N23 = 42'd2199023255552; // Fx<2, 42>
parameter fx_2___N24 = 44'd8796093022208; // Fx<2, 44>
parameter fx_2___N25 = 46'd35184372088832; // Fx<2, 46>
parameter fx_2___N26 = 48'd140737488355328; // Fx<2, 48>
parameter fx_2___N27 = 50'd562949953421312; // Fx<2, 50>
parameter fx_2___N28 = 52'd2251799813685248; // Fx<2, 52>
parameter fx_2___N29 = 54'd9007199254740992; // Fx<2, 54>
parameter fx_2___N30 = 56'd36028797018963968; // Fx<2, 56>
parameter fx_2___N31 = 58'd144115188075855872; // Fx<2, 58>
parameter fx_2___N32 = 60'd576460752303423488; // Fx<2, 60>







/// Two's complement
function [(N)-1:0] c2(input [(N)-1:0] a);
  c2 = ~a + 1'b1;
endfunction

// function automatic c2(a);
//   return unsigned'(-a);
// endfunction





/// Absolute value
function [N-1:0] abs(input [N-1:0] in);
  abs = in[N-1] == 0 ? in : c2(in);
endfunction

/// Returns minimum between two signed values
function [N-1:0] min(input [N-1:0] a, b);
  min = $signed(a) <= $signed(b) ? a : b;
endfunction

/// Returns maximum between two signed values
function [N-1:0] max(input [N-1:0] a, b);
  max = a >= b ? a : b;
endfunction

function is_negative(input [S:0] k);
  is_negative = k[S];
endfunction

function [N-1:0] shl(input [N-1:0] bits, input [N-1:0] rhs);
  shl = rhs[N-1] == 0 ? bits << rhs : bits >> c2(rhs);
endfunction







/// F64
parameter FLOAT_EXP_SIZE_F64 = 11;
parameter FLOAT_MANT_SIZE_F64 = 52;
/// F32
parameter FLOAT_EXP_SIZE_F32 = 8;
parameter FLOAT_MANT_SIZE_F32 = 23;
/// F16
parameter FLOAT_EXP_SIZE_F16 = 5;
parameter FLOAT_MANT_SIZE_F16 = 10;



endpackage: ppu_pkg
/* verilator lint_on DECLFILENAME */
/* verilator lint_on UNUSEDPARAM */
/* verilator lint_on VARHIDDEN */
module ppu_core_ops 
  import ppu_pkg::*;
#(
  parameter N = -1,
  parameter ES = -1
,parameter FSIZE = -1

)(
  input                                         clk_i,
  input                                         rst_i,
  input   ppu_pkg::posit_t                      p1_i,
  input   ppu_pkg::posit_t                      p2_i,
  input   ppu_pkg::posit_t                      p3_i,
  input   ppu_pkg::operation_e                  op_i,
  output  ppu_pkg::operation_e                  op_o,
  input                                         stall_i,
input       [(1+TE_BITS+FRAC_FULL_SIZE)-1:0]  float_fir_i,
  output     ppu_pkg::fir_t                     posit_fir_o,

  output  ppu_pkg::posit_t                      pout_o,
  ///
  output ppu_pkg::accumulator_t                 fixed_o
);






  localparam STAGES = 4;
  
  ppu_pkg::operation_e                              op[STAGES-1:0];

  ppu_pkg::posit_t                                  p1[STAGES-1:0],
                                                    p2[STAGES-1:0],
                                                    p3[STAGES-1:0];
  
  ppu_pkg::fir_t                                    fir1[STAGES-1:0],
                                                    fir2[STAGES-1:0],
                                                    fir3[STAGES-1:0];

  ppu_pkg::posit_special_t                          p_special[STAGES-1:0];

  ppu_pkg::accumulator_t                            fixed[STAGES-1:0];
  logic [((1 + TE_BITS + FRAC_FULL_SIZE) + 1)-1:0]  ops_result[STAGES-1:0];



  extraction #(
    .N            (N)
  ) extraction_i (
    .p1_i         (p1[0]),
    .p2_i         (p2[0]),
    .p3_i         (p3[0]),
    .op_i         (op[0]),
    .op_o         (op[1]),

    .fir1_o       (fir1[1]),
    .fir2_o       (fir2[1]),
    .fir3_o       (fir3[1]),

    .p_special_o  (p_special[1])
  );

    


  fir_ops #(
    .N              (N)
  ) fir_ops_inst (
    .clk_i          (clk_i),
    .rst_i          (rst_i),
    .op_i           (op[2]),
    .fir1_i         (fir1[2]),
    .fir2_i         (fir2[2]),
    .fir3_i         (fir3[2]),
    .ops_result_o   (ops_result[2]),
    .fixed_o        (fixed[2])
  );


  normalization #(
    .N              (N),
    .ES             (ES),
    .FIR_TOTAL_SIZE (1 + TE_BITS + FRAC_FULL_SIZE),

    .TE_BITS        (TE_BITS),
    .FRAC_FULL_SIZE (FRAC_FULL_SIZE)
  ) normalization_inst (
    .ops_result_i   (ops_result[3]),
    .p_special_i    (p_special[3]),
    .posit_o        (pout_o)
  );




  localparam _PIPE_DEPTH = 0;

  ////////////////////////////////////////////////////////////////////////////////////////////////////
  pipeline #(
    .PIPELINE_DEPTH (_PIPE_DEPTH),
    .DATA_WIDTH     ($bits({{op_i,   p1_i,   p2_i,   p3_i}}))
  ) pipeline_st0 (
    .clk_i          (clk_i),
    .rst_i          (rst_i),
    .data_in        ({op_i,   p1_i,   p2_i,   p3_i}),
    .data_out       ({op[0],  p1[0],  p2[0],  p3[0]})
  );
  ////////////////////////////////////////////////////////////////////////////////////////////////////
  pipeline #(
    .PIPELINE_DEPTH (_PIPE_DEPTH),
    .DATA_WIDTH     ($bits({op[1], fir1[1], fir2[1], fir3[1], p_special[1]}))
  ) pipeline_st1 (
    .clk_i          (clk_i),
    .rst_i          (rst_i),
    .data_in        ({op[1], fir1[1], fir2[1], fir3[1], p_special[1]}),
    .data_out       ({op[2], fir1[2], fir2[2], fir3[2], p_special[2]})
  );
  ////////////////////////////////////////////////////////////////////////////////////////////////////
  pipeline #(
    .PIPELINE_DEPTH (0),
    .DATA_WIDTH     ($bits({{fixed[2], ops_result[2], p_special[2]}}))
  ) pipeline_st2 (
    .clk_i          (clk_i),
    .rst_i          (rst_i),
    .data_in        ({fixed[2], op_i == F2P ? float_fir_i : ops_result[2], p_special[2]}),
    .data_out       ({fixed[3],                             ops_result[3], p_special[3]})
  );
  assign fixed_o = fixed[3];
  ////////////////////////////////////////////////////////////////////////////////////////////////////


//   logic [((1 + TE_BITS + FRAC_FULL_SIZE) + 1)-1:0] ops_wire_st0;
//   assign ops_wire_st0 =
// `ifdef FLOAT_TO_POSIT
//     (op_st1 == FLOAT_TO_POSIT) ? {float_fir_i, 1'b0} :
// `endif
//     ops_result;

  
  
  
  
  
  
  
  // posit to FIR
  assign posit_fir_o = fir2[2];


endmodule: ppu_core_ops
/* 
make -f Makefile_new.mk TOP=tb_accumulator
*/

module accumulator #(
  parameter FIXED_SIZE = -1
)(
  input logic                           clk_i,
  input logic                           rst_i,
  input logic                           start_i,
  input logic signed [FIXED_SIZE-1:0]   init_value_i,
  input logic signed [FIXED_SIZE-1:0]   fixed_i,
  output logic signed [FIXED_SIZE-1:0]  fixed_o
);

  logic signed [FIXED_SIZE-1:0] fixed_o_st1;

  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      fixed_o_st1 <= 'b0;
    end else begin
      fixed_o_st1 <= fixed_o;
    end
  end

  assign fixed_o = fixed_i + 
                   ((start_i == 1'b1) ? init_value_i : fixed_o_st1);

endmodule: accumulator

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
  output posit_special_t    p_special_o // `pout_special_or_trivial` + `is_special_or_trivial` tag
);

  // TODO: properly condition p3
  assign p3_o = p3_i;




  /*
  posit_t _p1, _p2;
  assign _p1 = p1_i;
  assign _p2 = (op_i == SUB) ? c2(p2_i) : p2_i;

  logic op_is_add_or_sub;
  assign op_is_add_or_sub = (op_i == ADD || op_i == SUB);

  assign {p1_o, p2_o} = (op_is_add_or_sub && abs(_p2) > abs(_p1)) ? {_p2, _p1} : {_p1, _p2};

  logic is_special_or_trivial;
  posit_t pout_special_or_trivial;

  */


  posit_t _p1, _p2;
  assign _p1 = p1_i;
  assign _p2 = (op_i == SUB) ? c2(p2_i) : p2_i;
  
  assign {p1_o, p2_o} = {_p1, _p2};

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
        op_i == F2P  /* check required to activate the rightmost mux */
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






/*
 
p1  p2  p3         (p1 * p2) + p3 
0    0     0              0      
0    0     NaN            NaN
0    0     p3             p3

0    NaN    0             NaN
0    NaN    NaN           NaN
0    NaN    p3            NaN

0    p2     0             0
0    p2     NaN           NaN
0    p2     p3            p3


*/

module extraction
  import ppu_pkg::*;
#(
  parameter N = -1
) (
  /// Input conditioning
  input  posit_t            p1_i,
  input  posit_t            p2_i,
  input  posit_t            p3_i,
  input  operation_e        op_i,

  output  operation_e       op_o,
  /// posit to fir
  output fir_t              fir1_o,
  output fir_t              fir2_o,
  output fir_t              fir3_o,

  output posit_special_t    p_special_o // `pout_special_or_trivial` + `is_special_or_trivial` tag
);

  
  posit_t p1_cond, p2_cond, p3_cond;

  input_conditioning #(
    .N          (N)
  ) input_conditioning (
    .p1_i       (p1_i),
    .p2_i       (p2_i),
    .p3_i       (p3_i),
    .op_i       (op_i),
    .p1_o       (p1_cond),
    .p2_o       (p2_cond),
    .p3_o       (p3_cond),
    .p_special_o(p_special_o)
  );

  posit_to_fir #(
    .N          (N),
    .ES         (ES)
  ) posit_to_fir1 (
    .p_cond_i   (p1_cond),
    .fir_o      (fir1_o)
  );

  wire [N-1:0] posit_in_posit_to_fir2;
  assign posit_in_posit_to_fir2 =
// `ifdef FLOAT_TO_POSIT
//     (op_st0 == P2F) ? p2_i :
// `endif
    p2_cond;


  posit_to_fir #(
    .N          (N),
    .ES         (ES)
  ) posit_to_fir2 (
    .p_cond_i   (posit_in_posit_to_fir2),
    .fir_o      (fir2_o)
  );


  posit_to_fir #(
    .N          (N),
    .ES         (ES)
  ) posit_to_fir3 (
    .p_cond_i   (p3_cond),
    .fir_o      (fir3_o)
  );

  assign op_o = op_i;

endmodule: extraction
module normalization 
  import ppu_pkg::*;
#(
  parameter N               = -1,
  parameter ES              = -1,

  parameter FIR_TOTAL_SIZE  = -1,

  parameter TE_BITS         = -1,
  parameter FRAC_FULL_SIZE  = -1
) (
  input ops_out_meta_t  ops_result_i,
  input posit_special_t p_special_i,
  output posit_t        posit_o
);


  posit_t pout_non_special;
  
  fir_to_posit #(
    .N                (N),
    .ES               (ES),
    .FIR_TOTAL_SIZE   (FIR_TOTAL_SIZE)
  ) fir_to_posit_inst (
    .ops_result_i     (ops_result_i),
    .posit_o          (pout_non_special)
  );


  logic is_special_or_trivial;
  logic pout_special_or_trivial;

  assign is_special_or_trivial = p_special_i.special_tag;
  assign pout_special_or_trivial = p_special_i.posit;


  assign posit_o = is_special_or_trivial ? pout_special_or_trivial : pout_non_special;

endmodule: normalization
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
    ? p_out_lut_sub : /* op_i == DIV */
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

  // assign total_exp = (1 << ES) * k_i + exp_i;


endmodule: total_exponent
/// Posit processing unit operations
module fir_ops 
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
  
  output ops_out_meta_t   ops_result_o,
  output accumulator_t    fixed_o
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
    
    .sign_o           (sign_out),
    .te_o             (te_out),
    .frac_o           (frac_out),
    .fixed_o          (fixed_o),
    .frac_truncated_o (frac_truncated)
  );


  
  assign ops_result_o.long_fir = {sign_out, te_out, frac_out};
  assign ops_result_o.frac_truncated = frac_truncated;

endmodule: fir_ops
module core_op 
  import ppu_pkg::*;
#(
  parameter TE_BITS         = -1,
  parameter MANT_SIZE       = -1,
  parameter FRAC_FULL_SIZE  = -1,
  parameter FX_M            = 31,
  parameter FX_B            = 64
) (
  input                         clk_i,
  input                         rst_i,
  input operation_e             op_i,
  
  input fir_t                   fir1_i,
  input fir_t                   fir2_i,
  input fir_t                   fir3_i,
  

  output logic                  sign_o,
  output exponent_t             te_o,
  output [(FRAC_FULL_SIZE)-1:0] frac_o,
  
  // accumulator value exported
  output [(FX_B)-1:0]           fixed_o,

  output                        frac_truncated_o
);

  wire [(MANT_ADD_RESULT_SIZE)-1:0] mant_out_add_sub;
  wire [(MANT_MUL_RESULT_SIZE)-1:0] mant_out_mul;
  wire [(MANT_DIV_RESULT_SIZE)-1:0] mant_out_div;


  logic sign_out_add_sub, sign_out_mul, sign_out_div;
  exponent_t te_out_add_sub, te_out_mul, te_out_div;
  wire frac_truncated_add_sub, frac_truncated_mul, frac_truncated_div;

  
  core_mul #(
    .TE_BITS                (TE_BITS),
    .MANT_SIZE              (MANT_SIZE),
    .MANT_MUL_RESULT_SIZE   (MANT_MUL_RESULT_SIZE)
  ) core_mul_inst (
    .clk_i                  (clk_i),
    .rst_i                  (rst_i),
    .sign1_i                (fir1_i.sign),
    .sign2_i                (fir2_i.sign),
    .te1_i                  (fir1_i.total_exponent),
    .te2_i                  (fir2_i.total_exponent),
    .mant1_i                (fir1_i.mant),
    .mant2_i                (fir2_i.mant),
    .sign_o                 (sign_out_mul),
    .te_o                   (te_out_mul),
    .mant_o                 (mant_out_mul),
    .frac_truncated_o       (frac_truncated_mul)
  );


  
  logic [(1+TE_BITS+MANT_MUL_RESULT_SIZE)-1:0] fir1_core_fma_accumulator;
  assign fir1_core_fma_accumulator = (op_i == FMADD_S || op_i == FMADD_C) ? {sign_out_mul, te_out_mul, mant_out_mul} : 'b0;

  fir_t fir2_core_fma_accumulator;
  assign fir2_core_fma_accumulator = (op_i == FMADD_S || op_i == FMADD_C) ? fir3_i : 'b0;
  
  
  localparam FIR_TE_SIZE = TE_BITS;
  localparam FIR_FRAC_SIZE = FRAC_FULL_SIZE;

  logic [(1+FIR_TE_SIZE+
          FIR_FRAC_SIZE)-1:0]   fir_fma;
  logic                         sign_out_fma;
  logic [TE_BITS-1:0]           te_out_fma;
  logic [(FRAC_FULL_SIZE)-1:0]  mant_out_fma;


core_fma_accumulator #(
    .N                      (N),
    .TE_BITS                (TE_BITS),
    .MANT_SIZE              (MANT_SIZE),
    .FRAC_FULL_SIZE         (FRAC_FULL_SIZE),
    .FX_M                   (FX_M),
    .FX_B                   (FX_B),
    .FIR_TE_SIZE            (FIR_TE_SIZE),
    .FIR_FRAC_SIZE          (FIR_FRAC_SIZE)
  ) core_fma_accumulator_inst (
    .clk_i                  (clk_i),
    .rst_i                  (rst_i),
    .op_i                   (op_i),
  
    .fir1_i                 (fir1_core_fma_accumulator),
    .fir2_i                 (fir2_core_fma_accumulator),

    .fir_fma                (fir_fma),
    .fixed_o                (fixed_o)
    // .frac_truncated_o       ()
  );


  assign {sign_out_fma, te_out_fma, mant_out_fma} = fir_fma;



  
//`define FMA_ONLY
add_sub #(
    .TE_BITS                (TE_BITS),
    .MANT_SIZE              (MANT_SIZE),
    .MANT_ADD_RESULT_SIZE   (MANT_ADD_RESULT_SIZE)
  ) add_sub_inst (
    .clk_i                  (clk_i),
    .rst_i                  (rst_i),
    
    .sign1_i                (fir1_i.sign),
    .sign2_i                (fir2_i.sign),
    .te1_i                  (fir1_i.total_exponent),
    .te2_i                  (fir2_i.total_exponent),
    .mant1_i                (fir1_i.mant),
    .mant2_i                (fir2_i.mant),

    .sign_o                 (sign_out_add_sub),
    .te_o                   (te_out_add_sub),
    .mant_o                 (mant_out_add_sub),
    .frac_truncated_o       (frac_truncated_add_sub)
  );



  core_div #(
    .TE_BITS                (TE_BITS),
    .MANT_SIZE              (MANT_SIZE),
    .MANT_DIV_RESULT_SIZE   (MANT_DIV_RESULT_SIZE)
  ) core_div_inst (
    .clk_i                  (clk_i),
    .rst_i                  (rst_i),
    .sign1_i                (fir1_i.sign),
    .sign2_i                (fir2_i.sign),
    .te1_i                  (fir1_i.total_exponent),
    .te2_i                  (fir2_i.total_exponent),
    .mant1_i                (fir1_i.mant),
    .mant2_i                (fir2_i.mant),
    .sign_o                 (sign_out_div),
    .te_o                   (te_out_div),
    .mant_o                 (mant_out_div),
    .frac_truncated_o       (frac_truncated_div)
  );




  wire [(FRAC_FULL_SIZE)-1:0] mant_out_core_op;
  assign mant_out_core_op = (op_i == ADD || op_i == SUB)
    ? mant_out_add_sub << (FRAC_FULL_SIZE - MANT_ADD_RESULT_SIZE) : op_i == MUL
    ? mant_out_mul << (FRAC_FULL_SIZE - MANT_MUL_RESULT_SIZE) : /* op_i == DIV */
      mant_out_div;


  assign sign_o = (op_i == FMADD_S || op_i == FMADD_C)
    ? sign_out_fma : (op_i == ADD || op_i == SUB)
    ? sign_out_add_sub : op_i == MUL
    ? sign_out_mul : /* op_i == DIV */
      sign_out_div;

  
  assign te_o = (op_i == FMADD_S || op_i == FMADD_C) 
    ? te_out_fma : (op_i == ADD || op_i == SUB)
    ? te_out_add_sub : op_i == MUL
    ? te_out_mul : /* op_i == DIV */
      te_out_div;


  // chopping off the two MSB representing the
  // non-fractional components i.e. ones and tens.
  assign frac_o = (op_i == FMADD_S || op_i == FMADD_C)
    ? mant_out_fma : op_i == DIV
    ? mant_out_core_op : /* ADD, SUB, and MUL */
      mant_out_core_op << 2;


  assign frac_truncated_o = op_i == MUL
    ? frac_truncated_mul : op_i == DIV
    ? frac_truncated_div : /* op_i == ADD || op_i == SUB */
      frac_truncated_add_sub;



endmodule: core_op
/// This module assumes that 
/// the input "1" is larger than "2".
/// 

module core_add_sub 
  import ppu_pkg::*;
#(
  parameter TE_BITS = -1,
  parameter MANT_SIZE = -1,
  parameter MANT_ADD_RESULT_SIZE = -1
) (
  input logic                         clk_i,
  input logic                         rst_i,
  input logic                         sign1_i,
  input logic                         sign2_i,
  input exponent_t                    te1_i,
  input exponent_t                    te2_i,
  input  [             MANT_SIZE-1:0] mant1_i,
  input  [             MANT_SIZE-1:0] mant2_i,
  
  output logic                        sign_o,
  output exponent_t                   te_o,
  output [(MANT_ADD_RESULT_SIZE)-1:0] mant_o,
  
  output                              frac_truncated_o
);


  function [(MANT_SIZE+MAX_TE_DIFF)-1:0] _c2(input [(MANT_SIZE+MAX_TE_DIFF)-1:0] a);
    _c2 = ~a + 1'b1;
  endfunction

  logic have_opposite_sign;
  assign have_opposite_sign = sign1_i ^ sign2_i;

  logic have_opposite_sign_st0, have_opposite_sign_st1;
  assign have_opposite_sign_st0 = have_opposite_sign;

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
  assign mant_sum_st0 = mant1_upshifted + (have_opposite_sign ? _c2(
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

  assign mant_o = have_opposite_sign_st1 ? {mant_out_core_sub  /*, 1'b0*/} : mant_out_core_add;

  assign te_o = te2_st1 + te_diff_updated;


assign te_diff_st1 = te_diff_st0;
  assign mant_sum_st1 = mant_sum_st0;
  assign have_opposite_sign_st1 = have_opposite_sign_st0;
  assign te2_st1 = te2_st0;



  assign sign_o = sign1_i;


endmodule: core_add_sub
module add_sub 
  import ppu_pkg::*;
#(
  parameter TE_BITS = -1,
  parameter MANT_SIZE = -1,
  parameter MANT_ADD_RESULT_SIZE = -1
) (
  input logic                         clk_i,
  input logic                         rst_i,

  input logic                         sign1_i,
  input logic                         sign2_i,
  input exponent_t                    te1_i,
  input exponent_t                    te2_i,
  input  [             MANT_SIZE-1:0] mant1_i,
  input  [             MANT_SIZE-1:0] mant2_i,
  
  output logic                        sign_o,
  output exponent_t                   te_o,
  output [(MANT_ADD_RESULT_SIZE)-1:0] mant_o,
  
  output                              frac_truncated_o
);

  
  logic                 sign1, sign2;
  exponent_t            te1, te2;
  logic [MANT_SIZE-1:0] mant1, mant2;

  
  router_core_add_sub #(
    .SIZE                 (1+TE_BITS+MANT_SIZE)
  ) router_core_add_sub_i (
    .port1_i              ({sign1_i, te1_i, mant1_i}),
    .port2_i              ({sign2_i, te2_i, mant2_i}),
    .port1_o              ({sign1, te1, mant1}),
    .port2_o              ({sign2, te2, mant2})
  );


  core_add_sub # (
    .TE_BITS              (TE_BITS),
    .MANT_SIZE            (MANT_SIZE),
    .MANT_ADD_RESULT_SIZE (MANT_ADD_RESULT_SIZE)
  ) core_add_sub_i (
    .clk_i                (clk_i),
    .rst_i                (rst_i),
    
    .sign1_i              (sign1),
    .sign2_i              (sign2),
    .te1_i                (te1),
    .te2_i                (te2),
    .mant1_i              (mant1),
    .mant2_i              (mant2),
  
    .sign_o               (sign_o),
    .te_o                 (te_o),
    .mant_o               (mant_o),
  
    .frac_truncated_o     (frac_truncated_o)
);


endmodule: add_sub
/// Router core_add_sub: routes the largest value FIR to port 1 of the adder and the smallest value to port 2
/// 
/// 

module router_core_add_sub
  import ppu_pkg::*;
#(
  parameter SIZE = -1
)(
  input logic [SIZE-1:0]  port1_i,
  input logic [SIZE-1:0]  port2_i,
  
  output logic [SIZE-1:0] port1_o,
  output logic [SIZE-1:0] port2_o
);

  // input unpacking
  logic                 sign1_i, sign2_i;
  exponent_t            te1_i, te2_i;
  logic [MANT_SIZE-1:0] mant1_i, mant2_i;

  
  assign {sign1_i, te1_i, mant1_i} = port1_i;
  assign {sign2_i, te2_i, mant2_i} = port2_i;


  // intermediate values
  logic                 sign1, sign2;
  exponent_t            te1, te2;
  logic [MANT_SIZE-1:0] mant1, mant2;


  
  assign {sign1, te1, mant1, sign2, te2, mant2} =
    ($signed(te1_i) <  $signed(te2_i)) ? {sign2_i, te2_i, mant2_i, sign1_i, te1_i, mant1_i} : // swap
    ($signed(te1_i) == $signed(te2_i)) ? (
                                            (mant1_i < mant2_i) ? {sign2_i, te2_i, mant2_i, sign1_i, te1_i, mant1_i} : 
                                                                  {sign1_i, te1_i, mant1_i, sign2_i, te2_i, mant2_i}
                                          ) : {sign1_i, te1_i, mant1_i, sign2_i, te2_i, mant2_i};
    
  
  assign port1_o = {sign1, te1, mant1};
  assign port2_o = {sign2, te2, mant2};


endmodule: router_core_add_sub
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

  /*
  cls #(
      .NUM_BITS(MANT_SUB_RESULT_SIZE)
  ) clz_inst (
      .bits               (mant),
      .val                (1'b0),
      .leading_set        (leading_zeros),
      .index_highest_set  ()
  );
  */

  wire is_valid;  // flag we dont care about here.

  lzc #(
    .NUM_BITS   (MANT_SUB_RESULT_SIZE)
  ) lzc_inst (
    .bits_i     (mant),
    .lzc_o      (leading_zeros),
    .valid_o    (is_valid)
  );

  assign new_te_diff = te_diff - leading_zeros;
  assign new_mant = (mant << leading_zeros);  // & ~(1 << (MANT_SUB_RESULT_SIZE-1));

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
  input logic                       sign1_i,
  input logic                       sign2_i,
  input  exponent_t                 te1_i,
  input  exponent_t                 te2_i,
  input  [           MANT_SIZE-1:0] mant1_i,
  input  [           MANT_SIZE-1:0] mant2_i,
  
  output logic                      sign_o,
  output exponent_t                 te_o,
  output [MANT_MUL_RESULT_SIZE-1:0] mant_o, // full output mantissa (no rounding)

  output                            frac_truncated_o
);

  exponent_t te_sum_st0, te_sum_st1;
  assign te_sum_st0 = te1_i + te2_i;

  wire [MANT_SUB_RESULT_SIZE-1:0] mant_mul;

//`define DUMPSTUFF


  wire mant_carry;
  assign mant_carry = mant_mul[MANT_MUL_RESULT_SIZE-1];

  assign te_o = mant_carry == 1'b1 ? te_sum_st1 + 1'b1 : te_sum_st1;
  assign mant_o = mant_carry == 1'b1 ? mant_mul >> 1 : mant_mul;

  assign frac_truncated_o = mant_carry && (mant_mul & 1);


  assign sign_o = sign1_i ^ sign2_i;

assign te_sum_st1 = te_sum_st0;
  assign mant_mul = mant1_i * mant2_i;


endmodule: core_mul
module core_fma_accumulator
  import ppu_pkg::*;
#(
  /// Posit size
  parameter N                                 = -1,
  /// Input FIR sizes
  parameter TE_BITS                           = -1,
  parameter MANT_SIZE                         = -1,
  parameter FRAC_FULL_SIZE                    = -1,
  /// Fixed point format
  parameter FX_M                              = 31,
  parameter FX_B                              = 64,
  /// output FIR sizes
  parameter FIR_TE_SIZE                       = -1,
  parameter FIR_FRAC_SIZE                     = -1
)(
  input logic                                   clk_i,
  input logic                                   rst_i,
  input operation_e                             op_i,
  
  input [(1+TE_BITS+MANT_MUL_RESULT_SIZE)-1:0]  fir1_i,
  input fir_t                                   fir2_i,

  output logic [(1+FIR_TE_SIZE+
                FIR_FRAC_SIZE)-1:0]             fir_fma,
  output logic [(FX_B)-1:0]                     fixed_o
  // output logic                               frac_truncated_o
);

  operation_e op_st1;
  always_ff @(posedge clk_i) op_st1 <= op_i;

  logic start_fma;
  //assign start_fma = (op_i == FMADD) && (op_st1 !== FMADD);
  assign start_fma = (op_i == FMADD_S);

  logic fma_valid;
  assign fma_valid = 1'b1; //  .... = op_i !== FMADD && op_st1 == FMADD ? 1'b1 : 'b0;

  
  logic [(FX_B)-1:0] fir1_fixed, fir2_fixed;
  fir_to_fixed #(
    .N              (2*N-3),   // TODO: Change this parameter to work with other values of N as well (ok with N=16)
    .FIR_TE_SIZE    (TE_BITS),
    .FIR_FRAC_SIZE  (MANT_MUL_RESULT_SIZE),
    .FX_M           (FX_M),
    .FX_B           (FX_B)
  ) fir_to_fixed_1_mul (
    .fir_i          (fir1_i),
    .fixed_o        (fir1_fixed)
  );


  fir_to_fixed #(
    .N              (N),
    .FIR_TE_SIZE    ($bits(fir2_i.total_exponent)),
    .FIR_FRAC_SIZE  ($bits(fir2_i.mant)),
    .FX_M           (FX_M),
    .FX_B           (FX_B)
  ) fir_to_fixed_2_fir3 (
    .fir_i          (fir2_i),
    .fixed_o        (fir2_fixed)
  );
  


  logic [(FX_B)-1:0] acc;
  accumulator #(
    .FIXED_SIZE   ($bits(fir1_fixed))
  ) accumulator_inst (
    .clk_i        (clk_i),
    .rst_i        (rst_i),
    .start_i      (start_fma),
    .init_value_i (fir2_fixed),
    .fixed_i      (fir1_fixed),
    .fixed_o      (acc)
  );


  fixed_to_fir #(
    .N              (N),
    .FIR_TE_SIZE    (TE_BITS),
    .FIR_FRAC_SIZE  (FRAC_FULL_SIZE),
    .FX_M           (FX_M),
    .FX_B           (FX_B)
  ) fixed_to_fir_acc (
    .fixed_i        (acc),
    .fir_o          (fir_fma)
  );



//assign fixed_o = op_i !== FMADD && op_st1 == FMADD ? acc : 'b0;
  assign fixed_o = acc;


endmodule: core_fma_accumulator
module core_div
  import ppu_pkg::*;
#(
  parameter TE_BITS = -1,
  parameter MANT_SIZE = -1,
  parameter MANT_DIV_RESULT_SIZE = -1
) (
  input                               clk_i,
  input                               rst_i,
  input logic                         sign1_i,
  input logic                         sign2_i,
  input  exponent_t                   te1_i,
  input  exponent_t                   te2_i,
  input  [             MANT_SIZE-1:0] mant1_i,
  input  [             MANT_SIZE-1:0] mant2_i,
  
  output logic                        sign_o,
  output exponent_t                   te_o,
  output [(MANT_DIV_RESULT_SIZE)-1:0] mant_o,
  
  output                              frac_truncated_o
);

  logic [MANT_SIZE-1:0] mant1_st0, mant1_st1;
  assign mant1_st0 = mant1_i;

  exponent_t te_diff_st0, te_diff_st1;
  assign te_diff_st0 = te1_i - te2_i;
  assign sign_o = sign1_i ^ sign2_i;

  wire [(MANT_DIV_RESULT_SIZE)-1:0] mant_div;

wire [(3*MANT_SIZE-4)-1:0] mant2_reciprocal;



initial $display("***** Using DIV with Fast reciprocate algorithm, no LUT *****");

  fast_reciprocal #(
    .SIZE               (MANT_SIZE)
  ) fast_reciprocal_inst (
    .fraction           (mant2_i),
    .one_over_fraction  (mant2_reciprocal)
  );


  wire [(2*MANT_SIZE)-1:0] x1;


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


  /// generated with `scripts/gen_fixed_point_values.py`
  wire [(SIZE)-1:0] fx_1_466  = fx_1_466___N16;
  wire [(2*SIZE-1)-1:0] fx_1_0012 = fx_1_0012___N16;


  assign b = fx_1_466 - a;
  assign c = (($signed(a) * $signed(b)) << 1) >> 1;
  assign d = fx_1_0012 - c;
  assign e = $signed(d) * $signed(b);
  assign out = e;

  /// full width output:
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
  
  /*

  num_i                     :   Fx<1, MS>
  x0_i                      :   Fx<1, 3MS - 4>

  num_i * x0_i              :   Fx<2, 4MS - 4>   -> Fx<2, 2MS> (downshifted by ((4MS-4) - (2MS) = 2MS - 4)

  2                         :   Fx<2, 2MS>

  2 - num_i * x0_i          :   Fx<2, 2MS>

  x0_2n                     :   Fx<1, 2MS>       -> x0_i downshifted by ((3MS - 3) - (2MS) = MS - 3)

  x0_2n * (2 - num_i * x0_i):   Fx<3, 4MS>       -> downshifted by ((4MS) - (2MS) - 2 = 2MS).
                                                                                  └── due to being:   000.101000111011101001110 vs      (what you have)
                                                                                                        0.10100011110                   (what you want)
  */


  wire [(4*MS-3)-1:0] _num_times_x0;
  assign _num_times_x0 = (num_i * x0_i) >> (2*MS - 4);
  
  
  logic [(2*MS)-1:0] num_times_x0_st0, num_times_x0_st1;
  assign num_times_x0_st0 = _num_times_x0;


  // generated with `scripts/gen_fixed_point_values.py`
  wire [(2*MS)-1:0] fx_2 = ppu_pkg::fx_2___N16;

  wire [(2*MS)-1:0] two_minus_num_x0;
  assign two_minus_num_x0 = fx_2 - num_times_x0_st1;


  logic [(2*MS)-1:0] x0_on_2n_bits_st0, x0_on_2n_bits_st1;
  assign x0_on_2n_bits_st0 = x0_i >> (MS - 4);

  wire [(4*MS)-1:0] _x1;
  assign _x1 = x0_on_2n_bits_st1 * two_minus_num_x0;

  // assign x1_o = _x1[(4*MS-1)-:MS];
  assign x1_o = _x1 >> (2*MS - 2);


  ///// ! implement `FF macro later on
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
  input                       frac_truncated_i, // new flag

  output [   K_BITS-1:0] k_o,
output [       ES-1:0] next_exp_o,

  output [MANT_SIZE-1:0] frac_o,

  // flags
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


  wire [MANT_LEN_BITS-1:0] frac_len;  // fix size
  assign frac_len = N - 1 - ES - reg_len;

wire [(ES+1)-1:0] es_actual_len;  // ES + 1 because it may potentially be negative.
  assign es_actual_len = min(ES, N - 1 - reg_len);


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

  assign k_o = regime_k;  // prev. k_unpacked which is wrong;

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
  ) == -(N - 2) ? /*$signed*/(                /* no longer signed. bug fixed 
                                                  Fri Apr  1 14:56:46 CEST 2022 
                                                  after P<16,1> 0x73 * 0xa4 
                                                  resulted in 0x1 rather than 
                                                  the correct result 0x2 */
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

  // u_bits = abs(bits)
  wire [N-1:0] u_bits;
  assign u_bits = sign_o == 0 ? bits_i : c2(bits_i);

  wire [S-1:0] leading_set,
               leading_set_2;

  // regime sign_o
  assign reg_s_o = u_bits[N-2];



      /*
          * Mon Jan  3 17:29:23 CET 2022
          * added this line to handle the only case in which the multiplier used to fail
          * (and other operations too since they depend on this module).
          * This is the case where the posit is of the type `0b1(zeroes)1`
      **/
      wire is_special_case;
      assign is_special_case = bits_i == { {1{1'b1}}, {N-2{1'b0}}, {1{1'b1}} };


      assign leading_set_2 = is_special_case ? (N-1) : leading_set; // temporary fix until you have
                                                                  // the time to embed this in the
                                                                  // general case (perhaps fixing cls.sv)

  assign k_o = reg_s_o == 1 ? leading_set_2 - 1 : c2(leading_set_2);


  assign reg_len_o = reg_s_o == 1 ? k_o + 2 : c2(k_o) + 1;


assign exp_o = (u_bits << (1 + reg_len_o)) >> (N - ES);


  wire [(S+1)-1:0] mant_len;
  assign mant_len = N - 1 - reg_len_o - ES;

  wire [FRAC_SIZE-1:0] frac;
  assign frac = (u_bits << (N - mant_len)) >> (N - mant_len);


  parameter MSB = 1 << (MANT_SIZE - 1);
  // assign mant_o = frac; // before
  assign mant_o = MSB | (frac << (MANT_SIZE-mant_len-1)); // after -> 1.frac


  wire [N-1:0] bits_cls_in = sign_o == 0 ? u_bits : ~u_bits;

  wire val = bits_cls_in[N-2];


  // //// count leading X
  // cls #(
  //     .NUM_BITS(N)
  // ) cls_inst (
  //     .bits               (bits_cls_in << 1), // strip sign_o bit and count ones from the left
  //     .val                (val),
  //     .leading_set        (leading_set),
  //     .index_highest_set  ()
  // );

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
  parameter N  = -1,  // dummy
  parameter ES = -1   // dummy
) (
  input posit_t   bits_i,
  output fir_t    fir_o
);

  wire                    _reg_s;  // unused, only to satisfy the linter
  wire [REG_LEN_BITS-1:0] _reg_len;  // unused, only to satisfy the linter

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
  input [ES-1:0]                exp,
  
  input [MANT_SIZE-1:0]           frac,
  output [N-1:0]                  posit
);

  wire [REG_LEN_BITS-1:0] reg_len;
  assign reg_len = $signed(k) >= 0 ? k + 2 : -$signed(k) + 1;

  wire [N-1:0] bits_packed;

  wire [N:0] regime_bits; // 1 bit longer than it could regularly fit in.

  assign regime_bits = is_negative(k) ? 1 : (shl(1, (k + 1)) - 1) << 1;




  assign bits_packed = (
    shl(sign, N-1) +
    shl(regime_bits, N - 1 - reg_len) + 
    shl(exp, N - 1 - reg_len - ES) +
    
    frac
  );

  assign posit =
    sign == 0
    ? bits_packed : c2(bits_packed & ~(1 << (N - 1)));

  /*
  ~(1'b1 << (N-1)) == {1'b0, {N-1{1'b1}}}
  */

endmodule: posit_encoder
module lzc #(
  parameter NUM_BITS = -1
) (
  input  [        NUM_BITS-1:0] bits_i,
  output [$clog2(NUM_BITS)-1:0] lzc_o,
  output                        valid_o
);
  // initial $display("Hello lzc.");
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
    end else if ((NUM_BITS & (NUM_BITS - 1))) begin : gen_blk2
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
/// Posit Processing Unit (PPU)
module ppu
  import ppu_pkg::*;
#(
  parameter WORD = 32,
  parameter FSIZE = 32,
  
  parameter N = 16,
  parameter ES = 1
) (
  input logic                           clk_i,
  input logic                           rst_i,
  input logic                           in_valid_i,
  input ppu_pkg::word_t                 operand1_i,
  input ppu_pkg::word_t                 operand2_i,
  input ppu_pkg::word_t                 operand3_i,
  input ppu_pkg::operation_e            op_i,
  output ppu_pkg::word_t result_o,
  output logic                          out_valid_o,
  output ppu_pkg::accumulator_t         fixed_o
);

  logic stall;
  
  ppu_pkg::fir_t posit_fir;
  ppu_pkg::posit_t p1, p2, p3, posit;

  assign p1 = operand1_i[N-1:0];
  assign p2 = operand2_i[N-1:0];
  assign p3 = operand3_i[N-1:0];


  ////////////////////////////////////////////////////////////
  /// float_fir, float_to_fir's side
  typedef struct packed {
    logic                           sign;
    logic [FLOAT_EXP_SIZE_F32-1:0]  total_exponent;
    logic [FLOAT_MANT_SIZE_F32-1:0] frac;
  } float_fir_float_to_fir_t;

  /// float_fir, ppu_core_ops' side
  typedef struct packed {
    logic                           sign;
    exponent_t                      total_exponent;
    logic [FRAC_FULL_SIZE-1:0]      frac;
  } float_fir_ppu_core_ops_t;
  ////////////////////////////////////////////////////////////

/// definition
  float_fir_float_to_fir_t float_fir_float_to_fir_o;
  float_fir_ppu_core_ops_t float_fir_ppu_core_ops_i;

  /// assignment
  assign float_fir_ppu_core_ops_i.sign            = float_fir_float_to_fir_o.sign;
  assign float_fir_ppu_core_ops_i.total_exponent  = float_fir_float_to_fir_o.total_exponent;
  assign float_fir_ppu_core_ops_i.frac            = {>>{float_fir_float_to_fir_o.frac}};

  // assign float_fir_ppu_core_ops_i = {>>{float_fir_float_to_fir_o.sign, float_fir_float_to_fir_o.total_exponent, float_fir_float_to_fir_o.frac}};


    /*   //no 
  //TODO fix streaming operation?
  logic [FRAC_FULL_SIZE-1:0] float_fir_frac;
  assign float_fir_frac = {>>{float_fir_float_to_fir_o.frac}};
  assign float_fir_ppu_core_ops_i.frac = {1'b1, float_fir_frac >> 1};
    */



  float_to_fir #(
    .FSIZE    (FSIZE)
  ) float_to_fir_inst (
    .clk_i    (clk_i),
    .rst_i    (rst_i),
    .bits_i   (operand1_i),
    .fir_o    (float_fir_float_to_fir_o)
  );




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
  .float_fir_i  (float_fir_ppu_core_ops_i),
    .posit_fir_o  (posit_fir),
  
    .pout_o       (posit),
    .fixed_o      (fixed_o)
  );



  

word_t float_out;

  fir_to_float #(
    .N            (N),
    .ES           (ES),
    .FSIZE        (FSIZE)
  ) fir_to_float_inst (
    .clk_i        (clk_i),
    .rst_i        (rst_i),
    .fir_i        (posit_fir),
    .float_o      (float_out)
  );

  assign result_o = (op_i == P2F) ? float_out : posit;


  
  
  
  ppu_control_unit #(
  ) ppu_control_unit_inst (
    .clk_i      (clk_i),
    .rst_i      (rst_i),
    .valid_i    (in_valid_i),
    .op_i       (op_i),
    .valid_o    (out_valid_o),
    .stall_o    (stall)
  );


endmodule: ppu
module pipeline #(
  parameter PIPELINE_DEPTH = 2,
  parameter DATA_WIDTH = 32 
)(
  input logic                     clk_i,
  input logic                     rst_i,
  input logic   [DATA_WIDTH-1:0]  data_in,
  output logic  [DATA_WIDTH-1:0]  data_out
);

  
  generate
    if (PIPELINE_DEPTH == 0) begin
      assign data_out = data_in;
    end else begin
      
      (*retiming_backward = 1 *)
      logic [DATA_WIDTH-1:0] pipeline_reg [PIPELINE_DEPTH-1:0] /*synthesis preserve*/;

      always_ff @(posedge clk_i) begin
        if (rst_i) begin
          for (int i = 0; i < PIPELINE_DEPTH; i++) begin
            pipeline_reg[i] <= 'b0;
          end
        end else begin
          pipeline_reg[0] <= data_in; 
          for (int i = 1; i < PIPELINE_DEPTH; i++) begin
            pipeline_reg[i] <= pipeline_reg[i-1];
          end
        end
      end

      assign data_out = pipeline_reg[PIPELINE_DEPTH-1];

    end
  endgenerate
  
  
endmodule: pipeline
// /// A wrapper around the actual ppu.
// module ppu_top 
//   import ppu_pkg::*;
// #(
//   parameter WORD = `WORD,
// `ifdef FLOAT_TO_POSIT
//   parameter FSIZE = `F,
// `endif
//   parameter N = `N,
//   parameter ES = `ES
// ) (
//   input  logic                    clk_i,
//   input  logic                    rst_i,
//   input  logic                    in_valid_i,
//   input  logic        [WORD-1:0]  operand1_i,
//   input  logic        [WORD-1:0]  operand2_i,
//   input  logic        [WORD-1:0]  operand3_i,
//   input  operation_e              op_i,
//   output logic        [WORD-1:0]  result_o,
//   output logic                    out_valid_o
// );


//   word_t operand1_st0_reg, operand2_st0_reg, operand3_st0_reg;
//                    // operand1_st1_reg, operand2_st1_reg, operand3_st1_reg;
//   word_t result_st0_reg,
//                    result_st1_reg;
//   logic [OP_BITS-1:0] op_st0_reg;
//                       // op_st1_reg;
//   logic in_valid_st0_reg;
//         // in_valid_st1_reg;
//   logic out_valid_st0_reg,
//         out_valid_st1_reg;

//   ppu #(
//     .WORD           (WORD),
//     `ifdef FLOAT_TO_POSIT
//       .FSIZE        (FSIZE),
//     `endif
//     .N              (N),
//     .ES             (ES)
//   ) ppu_inst (
//     .clk_i          (clk_i),
//     .rst_i          (rst_i),
//     .in_valid_i     (in_valid_st0_reg),
//     .operand1_i     (operand1_st0_reg),
//     .operand2_i     (operand2_st0_reg),
//     .operand3_i     (operand3_st0_reg),
//     .op_i           (operation_e'(op_st0_reg)),
//     .result_o       (result_st0_reg),
//     .out_valid_o    (out_valid_st0_reg)
// );


// always_ff @(posedge clk_i) begin
//   if (rst_i) begin
//     // inputs
//     in_valid_st0_reg <= '0;
//     operand1_st0_reg <= '0;
//     operand2_st0_reg <= '0;
//     operand3_st0_reg <= '0;
//     op_st0_reg <= '0;
//     // outputs

//     out_valid_st1_reg <= '0;
//     result_st1_reg <= '0;

//     out_valid_o <= '0;
//     result_o <= '0;
//   end else begin
//     // inputs
//     in_valid_st0_reg <= in_valid_i;
//     operand1_st0_reg <= operand1_i;
//     operand2_st0_reg <= operand2_i;
//     operand3_st0_reg <= operand3_i;
//     op_st0_reg <= op_i;
//     // outputs
    
//     out_valid_st1_reg <= out_valid_st0_reg;
//     result_st1_reg <= result_st0_reg;

//     out_valid_o <= out_valid_st1_reg;
//     result_o <= result_st1_reg;
//   end
// end

// endmodule: ppu_top



///////////////////////////////////////////////////////////////////////


/// A wrapper around the actual ppu.
module ppu_top 
  import ppu_pkg::*;
#(
  parameter PIPELINE_DEPTH  = 0,
  parameter WORD            = 32,
parameter FSIZE           = 32,

  parameter N               = 16,
  parameter ES              = 1
) (
  input  logic                    clk_i,
  input  logic                    rst_i,
  input  logic                    in_valid_i,
  /* dont change explicit type */
  input  logic        [WORD-1:0]  operand1_i,
  /* dont change explicit type */
  input  logic        [WORD-1:0]  operand2_i,
  /* dont change explicit type */
  input  logic        [WORD-1:0]  operand3_i,
  /* dont change explicit type */
  input  logic     [OP_BITS-1:0]  op_i,
  /* dont change explicit type */
  output logic        [WORD-1:0]  result_o,
  output logic                    out_valid_o,

  output logic      [64-1:0]   fixed_o
);

  word_t operand1_st0, operand2_st0, operand3_st0;

  word_t result_st0,
                   result_st1;
  logic [OP_BITS-1:0] op_st0;

  logic in_valid_st0;
        
  logic out_valid_st0,
        out_valid_st1;
  
  logic [64-1:0] fixed_st0;





  ppu #(
    .WORD           (WORD),
.FSIZE        (FSIZE),

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
    .out_valid_o    (out_valid_st0),
    .fixed_o        (fixed_st0)
);


  // initial $display($bits(in_valid_i) + $bits(op_i) + 3*$bits(operand1_i));

  localparam PIPELINE_DEPTH_FRONT = PIPELINE_DEPTH >= 1 ? 1 : 0;
  localparam PIPELINE_DEPTH_BACK  = PIPELINE_DEPTH >= 1 ? (PIPELINE_DEPTH - PIPELINE_DEPTH_FRONT) : 0;

  initial $display("PIPELINE_DEPTH_FRONT = %0d", PIPELINE_DEPTH_FRONT);
  initial $display("PIPELINE_DEPTH_BACK = %0d", PIPELINE_DEPTH_BACK);

  pipeline #(
    .PIPELINE_DEPTH   (PIPELINE_DEPTH_FRONT),
    .DATA_WIDTH   ($bits(in_valid_i) + $bits(op_i) + 3*$bits(operand1_i))
  ) pipeline_front (
    .clk_i        (clk_i),
    .rst_i        (rst_i),
    .data_in      ({in_valid_i,   op_i,   operand1_i,   operand2_i,   operand3_i}),
    .data_out     ({in_valid_st0, op_st0, operand1_st0, operand2_st0, operand3_st0})
  );

  pipeline #(
    .PIPELINE_DEPTH   (PIPELINE_DEPTH_BACK),
    .DATA_WIDTH   ($bits({result_st0, out_valid_st0, fixed_st0}))
  ) pipeline_back (
    .clk_i        (clk_i),
    .rst_i        (rst_i),
    .data_in      ({result_st0, out_valid_st0, fixed_st0}),
    .data_out     ({result_o,   out_valid_o,   fixed_o})
  );

endmodule: ppu_top
module ppu_control_unit 
  import ppu_pkg::*;
(
  input                      clk_i,
  input                      rst_i,
  input                      valid_i,
  input      operation_e     op_i,
  output                     valid_o,
  output logic               stall_o
);

//   logic valid;


// `ifdef TB_PIPELINE_FSM
//   localparam INIT = "INIT";
//   localparam ANY_OP = "ANY_OP";
//   reg [(300)-1:0] state_reg = 'hz;
// `elsif TB_PIPELINED
//   localparam INIT = "INIT";
//   localparam ANY_OP = "ANY_OP";
//   reg [(300)-1:0] state_reg = 'hz;
// `else
//   localparam INIT = 0;
//   localparam ANY_OP = 1;
//   reg [(1)-1:0] state_reg = INIT;
// `endif


//   wire [OP_BITS-1:0] __op = op;

//   always_ff @(posedge clk) begin
//     if (rst) begin
//       state_reg <= INIT;
//     end else begin
//       case (state_reg)
//         INIT: begin
//           if (valid_i) begin
//             state_reg <= ANY_OP;
//           end else begin  /* !valid_i */
//             state_reg <= INIT;
//           end
//         end
//         ANY_OP: begin
//           if (valid_i) begin
//             state_reg <= ANY_OP;
//           end else begin  /* !valid_i */
//             state_reg <= INIT;
//           end
//         end
//         default: begin
//           state_reg <= state_reg;
//         end
//       endcase
//     end
//   end

//   always @(*) begin
//     case (state_reg)
//       INIT: begin
//         stall_o = 0;
//         valid   = 0;
//       end
//       ANY_OP: begin
//         stall_o = 0;
//         valid   = 1;
//       end
//       default: begin
//         stall_o = 0;
//         valid   = 0;
//       end
//     endcase
//   end


//   logic valid_in_st0, valid_in_st1, valid_in_st2;
//   always_ff @(posedge clk) begin
//     if (rst) begin
//       valid_in_st0 <= 0;
//       valid_in_st1 <= 0;
//       valid_in_st2 <= 0;
//     end else begin
//       valid_in_st0 <= valid;
//       valid_in_st1 <= valid_in_st0;
//       valid_in_st2 <= valid_in_st1;
//     end
//   end

//   assign valid_o = valid_in_st1;


  pipeline #(
    .PIPELINE_DEPTH (0 * 2),
    .DATA_WIDTH     ($bits(valid_i))
  ) valid_signal_delay (
    .clk_i          (clk_i),
    .rst_i          (rst_i),
    .data_in        (valid_i),
    .data_out       (valid_o)
  );


endmodule: ppu_control_unit
module float_to_fir 
  import ppu_pkg::*;
#(
  parameter FSIZE = 64
)(
  input                                                       clk_i,
  input                                                       rst_i,
  input [FSIZE-1:0]                                           bits_i,
  output [(1 + FLOAT_EXP_SIZE_F32 + FLOAT_MANT_SIZE_F32)-1:0] fir_o
  );

  logic sign_st0, sign_st1;
  logic signed [FLOAT_EXP_SIZE_F32-1:0] exp_st0, exp_st1;
  logic [FLOAT_MANT_SIZE_F32-1:0] frac_st0, frac_st1;

  float_decoder #(
    .FSIZE  (FSIZE)
  ) float_decoder_inst (
    .bits   (bits_i),
    .sign   (sign_st0),
    .exp    (exp_st0),
    .frac   (frac_st0)
  );

  
  assign sign_st1 = sign_st0;
  assign exp_st1 = exp_st0;
  assign frac_st1 = frac_st0;

  assign fir_o = {sign_st1, exp_st1, frac_st1};

  
endmodule: float_to_fir

module fir_to_float 
  import ppu_pkg::*;
#(
  parameter N = -1,
  parameter ES = -1,
  parameter FSIZE = -1
)(
  input                   clk_i,
  input                   rst_i,
  input ppu_pkg::fir_t    fir_i,
  output [FSIZE-1:0]      float_o
);

  parameter FLOAT_EXP_SIZE = FLOAT_EXP_SIZE_F32;
  parameter FLOAT_MANT_SIZE = FLOAT_MANT_SIZE_F32;

  ppu_pkg::fir_t fir_st0, fir_st1;
  assign fir_st0 = fir_i;


  assign fir_st1 = fir_st0;
  

  wire posit_sign;
  exponent_t posit_te; // wire signed [TE_BITS-1:0] posit_te;
  wire [MANT_SIZE-1:0] posit_frac;

  assign {posit_sign, posit_te, posit_frac} = fir_st1;


  wire float_sign;
  wire signed [FLOAT_EXP_SIZE-1:0] float_exp;
  wire [FLOAT_MANT_SIZE-1:0] float_frac;

  assign float_sign = posit_sign;
  
  sign_extend #(
    .POSIT_TOTAL_EXPONENT_SIZE(TE_BITS),
    .FLOAT_EXPONENT_SIZE(FLOAT_EXP_SIZE)
  ) sign_extend_inst (
    .posit_total_exponent(posit_te),
    .float_exponent(float_exp)
  );      


  assign float_frac = posit_frac << (FLOAT_MANT_SIZE - MANT_SIZE + 1);

  float_encoder #(
    .FSIZE(FSIZE)
  ) float_encoder_inst (
    .sign(float_sign),
    .exp(float_exp),
    .frac(float_frac),
    .bits(float_o)
  );


endmodule: fir_to_float

module sign_extend 
#(
  parameter POSIT_TOTAL_EXPONENT_SIZE = 4,
  parameter FLOAT_EXPONENT_SIZE = 18
)(
  input [POSIT_TOTAL_EXPONENT_SIZE-1:0]    posit_total_exponent,
  output [FLOAT_EXPONENT_SIZE-1:0]                float_exponent
  );

  /*
  /// wasteful fancy way
  localparam EXPONENT_SIZE_DIFF = FLOAT_EXPONENT_SIZE - POSIT_TOTAL_EXPONENT_SIZE;

  assign float_exponent = posit_total_exponent >= 0 ? 
    posit_total_exponent : 
    ~( 
      {{EXPONENT_SIZE_DIFF{1'b0}}, (~posit_total_exponent + 1'b1)} 
    ) + 1'b1;
  */

  assign float_exponent = $signed(posit_total_exponent);

endmodule: sign_extend
module float_encoder 
  import ppu_pkg::*;
#(
  parameter FSIZE = 32
)(
  input                                       sign,
  input signed [FLOAT_EXP_SIZE_F32-1:0]       exp,
  input [FLOAT_MANT_SIZE_F32-1:0]             frac,
  output [FSIZE-1:0]                          bits
);

  wire [FLOAT_EXP_SIZE_F32-1:0] exp_bias = (1 << (FLOAT_EXP_SIZE_F32 - 1)) - 1;

  wire [FLOAT_EXP_SIZE_F32-1:0] exp_biased;
  assign exp_biased = exp + exp_bias;
  assign bits = {sign, exp_biased, frac};

endmodule: float_encoder





// `define STRINGIFY(DEFINE) $sformatf("%0s", `"DEFINE`")
/*


so far with the simplified assumption that the float fields are larger than the posit fields. also no dealing with subnormals
*/

module float_decoder 
  import ppu_pkg::*;
#(
  parameter FSIZE = 64
)(
  input [FSIZE-1:0]                         bits,
  output                                    sign,
  output signed [FLOAT_EXP_SIZE_F32-1:0]    exp,
  output [FLOAT_MANT_SIZE_F32-1:0]          frac
);

  localparam EXP_BIAS = (1 << (FLOAT_EXP_SIZE_F32 - 1)) - 1;

  assign sign = bits >> (FSIZE - 1) != 0;
  
  wire [FLOAT_EXP_SIZE_F32-1:0] biased_exp;
  assign biased_exp = bits[(FSIZE-1)-:FLOAT_EXP_SIZE_F32+1];    
      // ((bits & ((1 << (FSIZE - 1)) - 1)) >> FLOAT_MANT_SIZE) & ((1 << FLOAT_MANT_SIZE) - 1);

  assign exp = biased_exp - EXP_BIAS; // unbiased exponent
  assign frac = bits[FLOAT_MANT_SIZE_F32-1:0];  // bits & ((1 << FLOAT_MANT_SIZE) - 1);

endmodule: float_decoder



// `define tb_float_decoder 
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
  input ops_out_meta_t  ops_result_i, // TODO: fix frac_full. from `1.fff` to `.fff`.   `1.` must be appended here.
  output posit_t        posit_o
);

  long_fir_t fir;
  assign fir = ops_result_i.long_fir;
  
  logic frac_truncated;  // flag
  assign frac_truncated = ops_result_i.frac_truncated;

  logic sign;
  exponent_t te;
  logic [FRAC_FULL_SIZE-1:0] frac_full;
  assign {sign, te, frac_full} = fir;


  logic [MANT_SIZE-1:0] frac;
  logic [K_BITS-1:0] k;
logic [ES-1:0] next_exp;


  logic round_bit;
  logic sticky_bit;
  logic k_is_oob;
  logic non_zero_frac_field_size;
  

  pack_fields #(
    .N                (N),
    .ES               (ES)
  ) pack_fields_inst (
    .frac_full_i      (frac_full), // the whole mantissa w/o the leading 1. (let's call it `frac_full` to distinguish it from `frac`)
    .total_exp_i      (te),
    .frac_truncated_i (frac_truncated),

    .k_o              (k),
.next_exp_o       (next_exp),

    .frac_o           (frac), // the fractional part of the posit that actually fits in its (remaining) field. it's the most significant bits of `frac_full`.

    .round_bit        (round_bit),
    .sticky_bit       (sticky_bit),
    .k_is_oob         (k_is_oob),
    .non_zero_frac_field_size(non_zero_frac_field_size)
  );


  logic [N-1:0] posit_encoded;
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


  logic [N-1:0] posit_pre_sign;

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
module fir_to_fixed
#(
  /// Posit 
  /// In the future remove dependency from Posit size.
  parameter N             = -1,

  /// FIR parameters
  parameter FIR_TE_SIZE   = -1,
  parameter FIR_FRAC_SIZE = -1,
  
  /// Fixed point parameters (Fx<M,N>) without sign
  parameter FX_M = -1,
  parameter FX_B = -1
)(
  input   logic[(1+FIR_TE_SIZE+FIR_FRAC_SIZE)-1:0]    fir_i,
  output  logic[(FX_B)-1:0]                           fixed_o
);

  generate
    if ($bits(fir_i) >= $bits(fixed_o)) begin
      // $error("$bits(fir_i) must be larger than $bits(fixed_o)");  // CHANGE
    end
  endgenerate

  logic                           fir_sign;
  logic signed [FIR_TE_SIZE-1:0]  fir_te;
  logic [FIR_FRAC_SIZE-1:0]       fir_frac;
  assign {fir_sign, fir_te, fir_frac} = fir_i;


  logic[(FX_B)-1:0] fixed_tmp;
  
/*
  logic                   fixed_sign;
  logic [FX_M-1:0]        fixed_integer;
  logic [(FX_B-FX_M)-1:0] fixed_fraction;
  
  
  assign fixed_integer = fixed_tmp >> fir_te;
  assign fixed_fraction = fixed_tmp[(FX_B-FX_M)-1:0];
  assign fixed_sign = fir_sign;

  assign fixed_o = {fixed_sign, fixed_integer, fixed_fraction};
*/

  localparam MANT_MAX_LEN = N - 1 - 2; // -1: sign lenght, -2: regime min length

  assign fixed_tmp = fir_frac << (FX_B - FX_M - (MANT_MAX_LEN+1));

  logic fir_te_sign;
  assign fir_te_sign = fir_te >= 0;

  ppu_pkg::accumulator_t fixed_signless;
  assign fixed_signless = (fir_te >= 0) ? (fixed_tmp << fir_te) : (fixed_tmp >> (-fir_te));

  /// With correct sign
  assign fixed_o = fir_sign == 1'b0 ? fixed_signless : (~fixed_signless + 1'b1);

endmodule: fir_to_fixed
module fixed_to_fir
#(
  /// Posit 
  /// In the future remove dependency from Posit size.
  parameter N             = -1,

  /// FIR parameters
  parameter FIR_TE_SIZE   = -1,
  parameter FIR_FRAC_SIZE = -1,
  
  /// Fixed point parameters (Fx<M,N>) without sign
  parameter FX_M = -1,
  parameter FX_B = -1
)(
  input  logic[(FX_B)-1:0]                          fixed_i, // c2
  output logic[(1+FIR_TE_SIZE+FIR_FRAC_SIZE)-1:0]   fir_o
);

  logic                           fir_sign;
  logic signed [FIR_TE_SIZE-1:0]  fir_te;
  logic [FIR_FRAC_SIZE-1:0]       fir_frac;


  logic [$clog2(FX_B-1)-1:0] lzc_fixed; // FX_B-1 because sign is excluded
  logic lzc_valid;

  
  logic fixed_i_sign;
  assign fixed_i_sign = fixed_i[(FX_B)-1];

  logic [(FX_B)-1:0] fixed_i_abs;
  assign fixed_i_abs = (fixed_i_sign == 1'b0) ? fixed_i : (~fixed_i + 1'b1);
  
  lzc #(
    .NUM_BITS   (FX_B)
  ) lzc_inst (
    .bits_i     (fixed_i_abs),
    .lzc_o      (lzc_fixed),
    .valid_o    (lzc_valid)
  );


  assign fir_sign = fixed_i_sign;
  assign fir_te = FX_M - lzc_fixed;

  localparam MANT_MAX_LEN = N - 1 - 2; // -1: sign lenght, -2: regime min length

  

  logic [(FX_B)-1:0] fixed_i_abs_corrected;
  assign fixed_i_abs_corrected = (fir_te >= 0) ? (fixed_i_abs >> fir_te) : (fixed_i_abs << (-fir_te));

  logic [(FX_B-FX_M-1)-1:0] fixed_i_abs_corrected_frac_only;
  assign fixed_i_abs_corrected_frac_only = fixed_i_abs_corrected; // MS bits automatically cut off by the size


  localparam FX_N = FX_B        // fixed total length
                    - FX_M      // fixed integer part length
                    - 1;        // sign length

  generate
    if (FIR_FRAC_SIZE <= FX_N)  assign fir_frac = (fixed_i_abs_corrected[(1+FX_N)-1:0] >> (FX_N - FIR_FRAC_SIZE));
    else                        assign fir_frac = (fixed_i_abs_corrected[(1+FX_N)-1:0] << (FIR_FRAC_SIZE - FX_N));
  endgenerate

  assign fir_o = {fir_sign, fir_te, fir_frac};

endmodule: fixed_to_fir
