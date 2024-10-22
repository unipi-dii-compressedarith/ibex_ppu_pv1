// Copyright 2017 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    RISC-V Tracer                                              //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Traces the executed instructions                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
`ifndef VERILATOR


`include "zeroriscy_config.sv"

import zeroriscy_defines::*;
import zeroriscy_tracer_defines::*;


// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_S3 29:25
`define REG_D  11:07


module zeroriscy_tracer
#(
    parameter REG_ADDR_WIDTH      = 5
)
(
  // Clock and Reset
  input  logic        clk,
  input  logic        rst_n,

  input  logic        fetch_enable,
  input  logic [3:0]  core_id,
  input  logic [5:0]  cluster_id,

  input  logic [31:0] pc,
  input  logic [31:0] instr,
  input  logic        compressed,
  input  logic        id_valid,
  input  logic        is_decoding,
  input  logic        is_branch,
  input  logic        branch_taken,
  input  logic        pipe_flush,
  input  logic        mret_insn,
  input  logic        ecall_insn,
  input  logic        ebrk_insn,
  input  logic        csr_status,
  input  logic [31:0] rs1_value,
  input  logic [31:0] rs2_value,
  input  logic [31:0] lsu_value,

  input  logic [(REG_ADDR_WIDTH-1):0] ex_reg_addr,
  input  logic        ex_reg_we,
  input  logic [31:0] ex_reg_wdata,
  input  logic        data_valid_lsu,
  input  logic        ex_data_req,
  input  logic        ex_data_gnt,
  input  logic        ex_data_we,
  input  logic [31:0] ex_data_addr,
  input  logic [31:0] ex_data_wdata,

  input  logic [31:0] lsu_reg_wdata,

  input  logic [31:0] imm_u_type,
  input  logic [31:0] imm_uj_type,
  input  logic [31:0] imm_i_type,
  input  logic [11:0] imm_iz_type,
  input  logic [31:0] imm_z_type,
  input  logic [31:0] imm_s_type,
  input  logic [31:0] imm_sb_type
);
  integer      f;
  string       fn;
  integer      cycles;
  logic [ 4:0] rd, rs1, rs2, rs3;
`ifndef SV2V  
  typedef struct {
    logic [(REG_ADDR_WIDTH-1):0] addr;
    logic [31:0] value;
  } reg_t;

  typedef struct {
    logic [31:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [31:0] wdata;
    logic [31:0] rdata;
  } mem_acc_t;
  class instr_trace_t;
    time         simtime;
    integer      cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    string       str;
    reg_t        regs_read[$];
    reg_t        regs_write[$];
    mem_acc_t    mem_access[$];

    function new ();
      str        = "";
      regs_read  = {};
      regs_write = {};
      mem_access = {};
    endfunction

    function string regAddrToStr(input logic [(REG_ADDR_WIDTH-1):0] addr);
      begin
        if (addr < 10)
          return $sformatf(" x%0d", addr);
        else
          return $sformatf("x%0d", addr);
      end
    endfunction

    function void printInstrTrace();
      mem_acc_t mem_acc;
      begin
        $fwrite(f, "%t %15d %h %h %-36s", simtime,
                                          cycles,
                                          pc,
                                          instr,
                                          str);

        foreach(regs_write[i]) begin
          if (regs_write[i].addr != 0)
            $fwrite(f, " %s=%08x", regAddrToStr(regs_write[i].addr), regs_write[i].value);
        end

        foreach(regs_read[i]) begin
          if (regs_read[i].addr != 0)
            $fwrite(f, " %s:%08x", regAddrToStr(regs_read[i].addr), regs_read[i].value);
        end

        if (mem_access.size() > 0) begin
          mem_acc = mem_access.pop_front();

          $fwrite(f, "  PA:%08x", mem_acc.addr);
        end

        $fwrite(f, "\n");
      end
    endfunction

    function void printMnemonic(input string mnemonic);
      begin
        str = mnemonic;
      end
    endfunction // printMnemonic

    function void printRInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_read.push_back('{rs2, rs2_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
      end
    endfunction // printRInstr

    function void printIInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $signed(imm_i_type));
      end
    endfunction // printIInstr

    function void printIuInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, rd, rs1, imm_i_type);
      end
    endfunction // printIuInstr

    function void printUInstr(input string mnemonic);
      begin
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, {imm_u_type[31:12], 12'h000});
      end
    endfunction // printUInstr

    function void printUJInstr(input string mnemonic);
      begin
        regs_write.push_back('{rd, 'x});
        str =  $sformatf("%-16s x%0d, %0d", mnemonic, rd, $signed(imm_uj_type));
      end
    endfunction // printUJInstr

    function void printSBInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_read.push_back('{rs2, rs2_value});
        str =  $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rs1, rs2, $signed(imm_sb_type));
      end
    endfunction // printSBInstr

    function void printCSRInstr(input string mnemonic);
      logic [11:0] csr;
      begin
        csr = instr[31:20];

        regs_write.push_back('{rd, 'x});

        if (instr[14] == 1'b0) begin
          regs_read.push_back('{rs1, rs1_value});
          str = $sformatf("%-16s x%0d, x%0d, 0x%h", mnemonic, rd, rs1, csr);
        end else begin
          str = $sformatf("%-16s x%0d, 0x%h, 0x%h", mnemonic, rd, imm_z_type, csr);
        end
      end
    endfunction // printCSRInstr

    function void printLoadInstr();
      string mnemonic;
      logic [2:0] size;
      begin
        // detect reg-reg load and find size
        size = instr[14:12];
        if (instr[14:12] == 3'b111)
          size = instr[30:28];

        case (size)
          3'b000: mnemonic = "lb";
          3'b001: mnemonic = "lh";
          3'b010: mnemonic = "lw";
          3'b100: mnemonic = "lbu";
          3'b101: mnemonic = "lhu";
          3'b110: mnemonic = "p.elw";
          3'b011,
          3'b111: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        regs_write.push_back('{rd, 'x});

        if (instr[14:12] != 3'b111) begin
          // regular load
            regs_read.push_back('{rs1, rs1_value});
            str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rd, $signed(imm_i_type), rs1);
        end else begin
            printMnemonic("INVALID");
        end
      end
    endfunction

    function void printStoreInstr();
      string mnemonic;
      begin

        case (instr[13:12])
          2'b00:  mnemonic = "sb";
          2'b01:  mnemonic = "sh";
          2'b10:  mnemonic = "sw";
          2'b11: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        if (instr[14] == 1'b0) begin
          // regular store
            regs_read.push_back('{rs2, rs2_value});
            regs_read.push_back('{rs1, rs1_value});
            str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rs2, $signed(imm_s_type), rs1);
        end else begin
            printMnemonic("INVALID");
        end
      end
    endfunction // printSInstr

  endclass

  mailbox #(instr_trace_t) instr_ex = new ();
  mailbox #(instr_trace_t) instr_wb = new ();
  // cycle counter
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
      cycles = 0;
    else
      cycles = cycles + 1;
  end

  // open/close output file for writing
  initial
  begin
    wait(rst_n == 1'b1);
    wait(fetch_enable == 1'b1);
    $sformat(fn, "trace_core_%h_%h.log", cluster_id, core_id);
    $display("[TRACER] Output filename is: %s", fn);
    f = $fopen(fn, "w");
    $fwrite(f, "                Time          Cycles PC       Instr    Mnemonic\n");

  end

  final
  begin
    $fclose(f);
  end

  assign rd  = instr[`REG_D];
  assign rs1 = instr[`REG_S1];
  assign rs2 = instr[`REG_S2];
  assign rs3 = instr[`REG_S3];

  // log execution
  always @(negedge clk)
  begin
    instr_trace_t trace;
    mem_acc_t     mem_acc;
    // special case for WFI because we don't wait for unstalling there
    if ( (id_valid || mret_insn || ecall_insn || pipe_flush || ebrk_insn || csr_status || ex_data_req) && is_decoding)
    begin
      trace = new ();

      trace.simtime    = $time;
      trace.cycles     = cycles;
      trace.pc         = pc;
      trace.instr      = instr;

      // use casex instead of case inside due to ModelSim bug
      casex (instr)
        // Aliases
        32'h00_00_00_13:   trace.printMnemonic("nop");
        // Regular opcodes
        INSTR_LUI:        trace.printUInstr("lui");
        INSTR_AUIPC:      trace.printUInstr("auipc");
        INSTR_JAL:        trace.printUJInstr("jal");
        INSTR_JALR:       trace.printIInstr("jalr");
        // BRANCH
        INSTR_BEQ:        trace.printSBInstr("beq");
        INSTR_BNE:        trace.printSBInstr("bne");
        INSTR_BLT:        trace.printSBInstr("blt");
        INSTR_BGE:        trace.printSBInstr("bge");
        INSTR_BLTU:       trace.printSBInstr("bltu");
        INSTR_BGEU:       trace.printSBInstr("bgeu");
        // OPIMM
        INSTR_ADDI:       trace.printIInstr("addi");
        INSTR_SLTI:       trace.printIInstr("slti");
        INSTR_SLTIU:      trace.printIInstr("sltiu");
        INSTR_XORI:       trace.printIInstr("xori");
        INSTR_ORI:        trace.printIInstr("ori");
        INSTR_ANDI:       trace.printIInstr("andi");
        INSTR_SLLI:       trace.printIuInstr("slli");
        INSTR_SRLI:       trace.printIuInstr("srli");
        INSTR_SRAI:       trace.printIuInstr("srai");
        // OP
        INSTR_ADD:        trace.printRInstr("add");
        INSTR_SUB:        trace.printRInstr("sub");
        INSTR_SLL:        trace.printRInstr("sll");
        INSTR_SLT:        trace.printRInstr("slt");
        INSTR_SLTU:       trace.printRInstr("sltu");
        INSTR_XOR:        trace.printRInstr("xor");
        INSTR_SRL:        trace.printRInstr("srl");
        INSTR_SRA:        trace.printRInstr("sra");
        INSTR_OR:         trace.printRInstr("or");
        INSTR_AND:        trace.printRInstr("and");

        // PPU OP
        INSTR_PPU_ADD:        trace.printRInstr("padd");
        INSTR_PPU_SUB:        trace.printRInstr("psub");
        INSTR_PPU_MUL:        trace.printRInstr("pmul");
        INSTR_PPU_DIV:        trace.printRInstr("pdiv");
        INSTR_PPU_F2P:        trace.printRInstr("fcvt.p");
        INSTR_PPU_P2F:        trace.printRInstr("pcvt.f");

        // SYSTEM (CSR manipulation)
        INSTR_CSRRW:      trace.printCSRInstr("csrrw");
        INSTR_CSRRS:      trace.printCSRInstr("csrrs");
        INSTR_CSRRC:      trace.printCSRInstr("csrrc");
        INSTR_CSRRWI:     trace.printCSRInstr("csrrwi");
        INSTR_CSRRSI:     trace.printCSRInstr("csrrsi");
        INSTR_CSRRCI:     trace.printCSRInstr("csrrci");
        // SYSTEM (others)
        INSTR_ECALL:      trace.printMnemonic("ecall");
        INSTR_EBREAK:     trace.printMnemonic("ebreak");
        INSTR_MRET:       trace.printMnemonic("mret");
        INSTR_WFI:        trace.printMnemonic("wfi");
        // RV32M
        INSTR_PMUL:       trace.printRInstr("mul");
        INSTR_PMUH:       trace.printRInstr("mulh");
        INSTR_PMULHSU:    trace.printRInstr("mulhsu");
        INSTR_PMULHU:     trace.printRInstr("mulhu");
        INSTR_DIV:        trace.printRInstr("div");
        INSTR_DIVU:       trace.printRInstr("divu");
        INSTR_REM:        trace.printRInstr("rem");
        INSTR_REMU:       trace.printRInstr("remu");
        {25'b?, OPCODE_LOAD}:       trace.printLoadInstr();
        {25'b?, OPCODE_STORE}:      trace.printStoreInstr();
        default:           trace.printMnemonic("INVALID");
      endcase // unique case (instr)

        // replace register written back
        foreach(trace.regs_write[i]) begin
         if ((trace.regs_write[i].addr == ex_reg_addr) && ex_reg_we)
            trace.regs_write[i].value = ex_reg_wdata;
        end
        // look for data accesses and log them
        if (ex_data_req) begin

          if(~ex_data_gnt) begin
            //we wait until the the gnt comes
            do @(negedge clk);
            while (!ex_data_gnt);
          end

          mem_acc.addr = ex_data_addr;
          mem_acc.we   = ex_data_we;

          if (mem_acc.we)
            mem_acc.wdata = ex_data_wdata;
          else
            mem_acc.wdata = 'x;
          //we wait until the the data instruction ends
          do @(negedge clk);
          while (!data_valid_lsu);

          if (~mem_acc.we)
            //load operations
            foreach(trace.regs_write[i])
                trace.regs_write[i].value = lsu_reg_wdata;
          trace.mem_access.push_back(mem_acc);
        end
     trace.printInstrTrace();

    end
  end // always @ (posedge clk)
  `endif

endmodule
`endif
