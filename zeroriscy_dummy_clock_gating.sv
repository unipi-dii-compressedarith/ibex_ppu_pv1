// Dummy module for clock gating
//       cluster_clock_gating CG_Inst
//      (
//       .clk_i     ( clk_int                               ),
//        .en_i      ( waddr_onehot_a[x]                     ),
//        .test_en_i ( test_en_i                             ),
//        .clk_o     ( mem_clocks[x]                         )
//      );
module cluster_clock_gating (
    input  wire clk_i,
    input  wire en_i,
    input  wire test_en_i,
    output wire clk_o
    );
    
    // Simple passthrough of clk_i to clk_o
    assign clk_o = clk_i;

    // End of module
endmodule