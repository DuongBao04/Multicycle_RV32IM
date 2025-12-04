`include "defines.vh"

module DatapathMultiCycle (
  input                    clk,
  input                    rst,
  output reg               halt,
  output     [`REG_SIZE:0] pc_to_imem,
  input      [`REG_SIZE:0] inst_from_imem,
  // addr_to_dmem is a read-write port
  output reg [`REG_SIZE:0] addr_to_dmem,
  input      [`REG_SIZE:0] load_data_from_dmem,
  output reg [`REG_SIZE:0] store_data_to_dmem,
  output reg [        3:0] store_we_to_dmem
);

  // TODO: your code here (largely based on homework #3)
  // components of the instruction
  wire [           6:0] inst_funct7;
  wire [           4:0] inst_rs2;
  wire [           4:0] inst_rs1;
  wire [           2:0] inst_funct3;
  wire [           4:0] inst_rd;
  wire [`OPCODE_SIZE:0] inst_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {inst_funct7, inst_rs2, inst_rs1, inst_funct3, inst_rd, inst_opcode} = inst_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = inst_from_imem[31:20];
  wire [ 4:0] imm_shamt = inst_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s = {inst_funct7, inst_rd};

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:1], imm_b[11], imm_b[0]} = {inst_funct7, inst_rd, 1'b0};

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} =
         {inst_from_imem[31:12], 1'b0};

  // U type
  wire [`REG_SIZE:0] imm_u = {inst_from_imem[31:12], 12'b0};

  wire [`REG_SIZE:0] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE:0] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE:0] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE:0] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam [`OPCODE_SIZE:0] OpLoad    = 7'b00_000_11;
  localparam [`OPCODE_SIZE:0] OpStore   = 7'b01_000_11;
  localparam [`OPCODE_SIZE:0] OpBranch  = 7'b11_000_11;
  localparam [`OPCODE_SIZE:0] OpJalr    = 7'b11_001_11;
  localparam [`OPCODE_SIZE:0] OpMiscMem = 7'b00_011_11;
  localparam [`OPCODE_SIZE:0] OpJal     = 7'b11_011_11;

  localparam [`OPCODE_SIZE:0] OpRegImm  = 7'b00_100_11;
  localparam [`OPCODE_SIZE:0] OpRegReg  = 7'b01_100_11;
  localparam [`OPCODE_SIZE:0] OpEnviron = 7'b11_100_11;

  localparam [`OPCODE_SIZE:0] OpAuipc   = 7'b00_101_11;
  localparam [`OPCODE_SIZE:0] OpLui     = 7'b01_101_11;

  wire inst_lui    = (inst_opcode == OpLui    );
  wire inst_auipc  = (inst_opcode == OpAuipc  );
  wire inst_jal    = (inst_opcode == OpJal    );
  wire inst_jalr   = (inst_opcode == OpJalr   );

  wire inst_beq    = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b000);
  wire inst_bne    = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b001);
  wire inst_blt    = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b100);
  wire inst_bge    = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b101);
  wire inst_bltu   = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b110);
  wire inst_bgeu   = (inst_opcode == OpBranch ) & (inst_from_imem[14:12] == 3'b111);

  wire inst_lb     = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b000);
  wire inst_lh     = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b001);
  wire inst_lw     = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b010);
  wire inst_lbu    = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b100);
  wire inst_lhu    = (inst_opcode == OpLoad   ) & (inst_from_imem[14:12] == 3'b101);

  wire inst_sb     = (inst_opcode == OpStore  ) & (inst_from_imem[14:12] == 3'b000);
  wire inst_sh     = (inst_opcode == OpStore  ) & (inst_from_imem[14:12] == 3'b001);
  wire inst_sw     = (inst_opcode == OpStore  ) & (inst_from_imem[14:12] == 3'b010);

  wire inst_addi   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b000);
  wire inst_slti   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b010);
  wire inst_sltiu  = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b011);
  wire inst_xori   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b100);
  wire inst_ori    = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b110);
  wire inst_andi   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b111);

  wire inst_slli   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b001) &
                     (inst_from_imem[31:25] == 7'd0);
  wire inst_srli   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b101) &
                     (inst_from_imem[31:25] == 7'd0);
  wire inst_srai   = (inst_opcode == OpRegImm ) & (inst_from_imem[14:12] == 3'b101) &
                     (inst_from_imem[31:25] == 7'b0100000);

  wire inst_add    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b000) &
                     (inst_from_imem[31:25] == 7'd0);
  wire inst_sub    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b000) &
                     (inst_from_imem[31:25] == 7'b0100000);
  wire inst_sll    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b001) &
                     (inst_from_imem[31:25] == 7'd0);
  wire inst_slt    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b010) &
                     (inst_from_imem[31:25] == 7'd0);
  wire inst_sltu   = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b011) &
                     (inst_from_imem[31:25] == 7'd0);
  wire inst_xor    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b100) &
                     (inst_from_imem[31:25] == 7'd0);
  wire inst_srl    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b101) &
                     (inst_from_imem[31:25] == 7'd0);
  wire inst_sra    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b101) &
                     (inst_from_imem[31:25] == 7'b0100000);
  wire inst_or     = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b110) &
                     (inst_from_imem[31:25] == 7'd0);
  wire inst_and    = (inst_opcode == OpRegReg ) & (inst_from_imem[14:12] == 3'b111) &
                     (inst_from_imem[31:25] == 7'd0);

  wire inst_mul    = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1) &
                     (inst_from_imem[14:12] == 3'b000);
  wire inst_mulh   = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1) &
                     (inst_from_imem[14:12] == 3'b001);
  wire inst_mulhsu = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1) &
                     (inst_from_imem[14:12] == 3'b010);
  wire inst_mulhu  = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1) &
                     (inst_from_imem[14:12] == 3'b011);
  wire inst_div    = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1) &
                     (inst_from_imem[14:12] == 3'b100);
  wire inst_divu   = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1) &
                     (inst_from_imem[14:12] == 3'b101);
  wire inst_rem    = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1) &
                     (inst_from_imem[14:12] == 3'b110);
  wire inst_remu   = (inst_opcode == OpRegReg ) & (inst_from_imem[31:25] == 7'd1) &
                     (inst_from_imem[14:12] == 3'b111);

  wire inst_ecall  = (inst_opcode == OpEnviron) & (inst_from_imem[31:7] == 25'd0);
  wire inst_fence  = (inst_opcode == OpMiscMem);
  
  wire is_div_op      = inst_div | inst_divu | inst_rem | inst_remu; //check divider op  
  reg  [3:0] div_counter;  
  wire       div_is_signed = inst_div | inst_rem;                    //check signed divide
  
  always @(posedge clk) begin
    if (rst) begin
      div_counter <= 0;
    end else begin
      if (is_div_op) begin
        if (div_counter < 8) 
          div_counter <= div_counter + 1;
        else 
          div_counter <= 0; 
      end else begin
        div_counter <= 0;
      end
    end
  end
  
  assign stall = is_div_op && (div_counter < 8); //stall if div
  
  // program counter
  reg [`REG_SIZE:0] pcNext, pcCurrent;

  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      if (!stall) pcCurrent <= pcNext;
    end
  end

  assign pc_to_imem = pcCurrent;
  
  wire [`REG_SIZE:0] rs1_data;
  wire [`REG_SIZE:0] rs2_data;
  
  reg                rf_we;
  reg [        4:0]  rf_rd;    
  reg [`REG_SIZE:0]  rf_wdata;
    
  RegFile rf (
    .clk      (clk),
    .rst      (rst),
    .we       (rf_we),
    .rd       (rf_rd),
    .rd_data  (rf_wdata),
    .rs1      (inst_rs1),
    .rs2      (inst_rs2),
    .rs1_data (rs1_data),
    .rs2_data (rs2_data)
  );
  
  wire [31:0] div_quotient;
  wire [31:0] div_remainder;
  
  DividerPipeline divider_inst (
    .clk         (clk),
    .rst         (rst),
    .stall       (1'b0),           
    .is_signed   (div_is_signed),   
    .i_dividend  (rs1_data),
    .i_divisor   (rs2_data),
    .o_remainder (div_remainder),
    .o_quotient  (div_quotient)
  );
  
  reg  [1:0]        ALUSrcA_Sel; // 00: rs1_data, 01: pcCurrent
  reg  [1:0]        ALUSrcB_Sel; // 00: rs2_data, 01: imm_i_sext
  wire [`REG_SIZE:0] ALUSrcA;
  wire [`REG_SIZE:0] ALUSrcB;
  wire [`REG_SIZE:0] ALUResult;
  wire               ALUZero;
  
  reg [3:0] ALU_Op;

  assign ALUSrcA = (ALUSrcA_Sel == 2'b00) ? rs1_data : pcCurrent;

  assign ALUSrcB = (ALUSrcB_Sel == 2'b00) ? rs2_data    :
                   (ALUSrcB_Sel == 2'b01) ? imm_i_sext  :
                   (ALUSrcB_Sel == 2'b10) ? imm_s_sext  :
                   (ALUSrcB_Sel == 2'b11) ? imm_u       :     
                   32'hDEADBEEF;

  localparam [3:0] ADD    = 4'b0000;
  localparam [3:0] SUB    = 4'b0001;
  localparam [3:0] AND    = 4'b0010;
  localparam [3:0] OR     = 4'b0011;
  localparam [3:0] XOR    = 4'b0100;
  localparam [3:0] SLT    = 4'b0101; // Set Less Than (Signed)
  localparam [3:0] SLTU   = 4'b0110; // Set Less Than (Unsigned)
  localparam [3:0] SLL    = 4'b0111; // Shift Left Logical
  localparam [3:0] SRL    = 4'b1000; // Shift Right Logical
  localparam [3:0] SRA    = 4'b1001; // Shift Right Arithmetic
  localparam [3:0] MUL    = 4'b1010;
  localparam [3:0] MULH   = 4'b1011;
  localparam [3:0] MULHSU = 4'b1100;
  localparam [3:0] MULHU  = 4'b1101;
    
  ALU alu (
    .A      (ALUSrcA),
    .B      (ALUSrcB),
    .ALUOp  (ALU_Op),
    .result (ALUResult),
    .Zero   (ALUZero)
  );
    
  reg  [1:0]        wback_sel; 
  reg  [`REG_SIZE:0] load_data; 
  wire [`REG_SIZE:0] wback_data;
    
  assign wback_data = (wback_sel == 2'b00) ? ALUResult      :
                      (wback_sel == 2'b01) ? imm_u          :
                      (wback_sel == 2'b10) ? (pcCurrent + 4) : load_data;

  wire [`REG_SIZE:0] mem_addr      = ALUResult;
  wire [        1:0] mem_addr_bits = mem_addr[1:0];
  wire [`REG_SIZE:0] load_word     = load_data_from_dmem;
  reg  [7:0]         load_byte_selected;
  reg  [15:0]        load_halfword_selected;

  wire [`REG_SIZE:0] branchTarget = pcCurrent + imm_b_sext;
  wire [`REG_SIZE:0] jalTarget    = pcCurrent + imm_j_sext;
    
  reg illegal_inst;
    
  always @(*) begin
    illegal_inst = 1'b0;
        
    halt = 0;

    // Store
    addr_to_dmem       = ALUResult;   // default store address
    store_data_to_dmem = rs2_data;    // default store data
    store_we_to_dmem   = 0;
        
    // Control signal
    rf_we     = 0;
    rf_rd     = 0;
    wback_sel = 0;
    rf_wdata  = wback_data;
        
    ALUSrcA_Sel = 2'b00; 
    ALUSrcB_Sel = 2'b00; 
    ALU_Op      = ADD;       
        
    pcNext    = pcCurrent + 4;
    load_data = load_word;
        
    case (inst_opcode)
      OpLui: begin
        // TODO: start here by implementing lui
        rf_we     = (inst_rd != 5'd0);
        rf_rd     = inst_rd;
        wback_sel = 2'b01;
      end
          
      OpAuipc: begin
        // rd = pcCurrent + imm_u
        rf_we       = (inst_rd != 5'd0);
        rf_rd       = inst_rd;
        ALUSrcA_Sel = 2'b01; // A = pcCurrent
        ALUSrcB_Sel = 2'b11; // B = imm_u
        ALU_Op      = ADD;
        wback_sel   = 2'b00; // 00 = ALUResult
      end
          
      OpJal: begin
        // rd = pc + 4; pc = pc + imm_j_sext
        rf_we     = (inst_rd != 5'd0);
        rf_rd     = inst_rd;
        wback_sel = 2'b10; // 10 = pc4
        pcNext    = jalTarget;
      end
          
      OpJalr: begin
        // rd = pc + 4; pc = (rs1 + imm_i_sext) & ~1
        rf_we       = (inst_rd != 5'd0);
        rf_rd       = inst_rd;
        wback_sel   = 2'b10; // 10 = pc4
        ALUSrcA_Sel = 2'b00; // A = rs1_data
        ALUSrcB_Sel = 2'b01; // B = imm_i_sext
        ALU_Op      = ADD;
        pcNext      = ALUResult & 32'hFFFFFFFE; // (mask bit 0)
      end
          
      OpLoad: begin
        // rd = mem[rs1 + imm_i_sext]
        ALUSrcA_Sel = 2'b00; // ALU A = rs1_data
        ALUSrcB_Sel = 2'b01; // ALU B = imm_i_sext
        ALU_Op      = ADD;
            
        addr_to_dmem = ALUResult; // G?i ??a ch? ??n dmem
            
        rf_we     = (inst_rd != 5'd0);
        rf_rd     = inst_rd;
        wback_sel = 2'b11; // 11 = load_data_
            
        case (mem_addr_bits)
          2'b00: begin
            load_byte_selected     = load_word[7:0];
            load_halfword_selected = load_word[15:0];
          end
          2'b01: begin
            load_byte_selected     = load_word[15:8];
            load_halfword_selected = load_word[15:0]; // misaligned
          end
          2'b10: begin
            load_byte_selected     = load_word[23:16];
            load_halfword_selected = load_word[31:16];
          end
          default: begin // 2'b11
            load_byte_selected     = load_word[31:24];
            load_halfword_selected = load_word[31:16]; // misaligned
          end
        endcase
    
        if (inst_lb) begin // sign-extend byte
          load_data = {{24{load_byte_selected[7]}}, load_byte_selected};
        end else if (inst_lbu) begin // zero-extend byte
          load_data = {24'b0, load_byte_selected};
        end else if (inst_lh) begin // sign-extend halfword
          load_data = {{16{load_halfword_selected[15]}}, load_halfword_selected};
        end else if (inst_lhu) begin // zero-extend halfword
          load_data = {16'b0, load_halfword_selected};
        end else if (inst_lw) begin // full word
          load_data = load_word;
        end else begin // default
          load_data = load_word;
        end
      end      
          
      OpStore: begin
        // mem[rs1 + imm_s_sext] = rs2
        ALUSrcA_Sel = 2'b00; 
        ALUSrcB_Sel = 2'b10; 
        ALU_Op      = ADD;
    
        addr_to_dmem = ALUResult; 
        rf_we        = 0; // store không ghi vào reg file
    
        if (inst_sw) begin
          store_we_to_dmem   = 4'b1111;
          store_data_to_dmem = rs2_data;
        end else if (inst_sh) begin
          if (mem_addr_bits[1] == 1'b0) begin // 00
            store_we_to_dmem   = 4'b0011;
            store_data_to_dmem = {16'b0, rs2_data[15:0]};
          end else begin // 10
            store_we_to_dmem   = 4'b1100;
            store_data_to_dmem = {rs2_data[15:0], 16'b0};
          end
        end else if (inst_sb) begin
          case (mem_addr_bits)
            2'b00: begin
              store_we_to_dmem   = 4'b0001;
              store_data_to_dmem = {24'b0, rs2_data[7:0]};
            end
            2'b01: begin
              store_we_to_dmem   = 4'b0010;
              store_data_to_dmem = {16'b0, rs2_data[7:0], 8'b0};
            end
            2'b10: begin
              store_we_to_dmem   = 4'b0100;
              store_data_to_dmem = {8'b0, rs2_data[7:0], 16'b0};
            end
            default: begin // 2'b11
              store_we_to_dmem   = 4'b1000;
              store_data_to_dmem = {rs2_data[7:0], 24'b0};
            end
          endcase
        end else begin
          illegal_inst = 1'b1;
        end
      end
          
      OpRegImm: begin
        ALUSrcA_Sel = 2'b00;
        ALUSrcB_Sel = 2'b01;
        rf_we       = (inst_rd != 5'd0);
        rf_rd       = inst_rd;
        wback_sel   = 2'b00;
            
        if      (inst_addi)  ALU_Op = ADD;
        else if (inst_slti)  ALU_Op = SLT;
        else if (inst_sltiu) ALU_Op = SLTU;
        else if (inst_xori)  ALU_Op = XOR;
        else if (inst_ori)   ALU_Op = OR;
        else if (inst_andi)  ALU_Op = AND;
        else if (inst_slli)  ALU_Op = SLL;
        else if (inst_srli)  ALU_Op = SRL;
        else if (inst_srai)  ALU_Op = SRA;
        else                 illegal_inst = 1'b1;
      end
          
      OpRegReg: begin
        ALUSrcA_Sel = 2'b00;
        ALUSrcB_Sel = 2'b00;
                
        if (is_div_op) begin
          if (stall) begin
            rf_we  = 0;              
            pcNext = pcCurrent;    
            rf_rd  = 0;
          end else begin
            rf_we = (inst_rd != 5'd0);
            rf_rd = inst_rd;
            if (inst_div || inst_divu)
              rf_wdata = div_quotient;
            else
              rf_wdata = div_remainder;
                        
            pcNext = pcCurrent + 4; 
          end
        end else begin
          rf_we     = (inst_rd != 5'd0);
          rf_rd     = inst_rd;
          wback_sel = 2'b00; // ALUResult

          if      (inst_add)    ALU_Op = ADD;
          else if (inst_sub)    ALU_Op = SUB;
          else if (inst_slt)    ALU_Op = SLT;
          else if (inst_sltu)   ALU_Op = SLTU;
          else if (inst_xor)    ALU_Op = XOR;
          else if (inst_or)     ALU_Op = OR;
          else if (inst_and)    ALU_Op = AND;
          else if (inst_sll)    ALU_Op = SLL;
          else if (inst_srl)    ALU_Op = SRL;
          else if (inst_sra)    ALU_Op = SRA;
          else if (inst_mul)    ALU_Op = MUL;
          else if (inst_mulh)   ALU_Op = MULH;
          else if (inst_mulhsu) ALU_Op = MULHSU;
          else if (inst_mulhu)  ALU_Op = MULHU;
          else                  illegal_inst = 1'b1;
        end
      end
           
      OpBranch: begin
        rf_we       = 0;
        ALUSrcA_Sel = 2'b00;
        ALUSrcB_Sel = 2'b00;
            
        if (inst_beq) begin
          ALU_Op = SUB;
          if (ALUZero) begin
            pcNext = branchTarget;
          end
        end else if (inst_bne) begin
          ALU_Op = SUB;
          if (!ALUZero) begin
            pcNext = branchTarget;
          end
        end else if (inst_blt) begin
          ALU_Op = SLT;
          if (ALUResult == 1) begin
            pcNext = branchTarget;
          end
        end else if (inst_bge) begin 
          ALU_Op = SLT;
          if (ALUResult == 0) begin
            pcNext = branchTarget;
          end
        end else if (inst_bltu) begin 
          ALU_Op = SLTU;
          if (ALUResult == 1) begin
            pcNext = branchTarget;
          end
        end else if (inst_bgeu) begin 
          ALU_Op = SLTU;
          if (ALUResult == 0) begin
            pcNext = branchTarget;
          end
        end else begin
          illegal_inst = 1'b1;
        end
      end      
          
      OpEnviron: begin
        if (inst_ecall) begin
          halt = 1;
        end else begin
          illegal_inst = 1'b1;
        end
      end
             
      default: begin
        illegal_inst = 1'b1;
      end
    endcase  
  end
    
endmodule