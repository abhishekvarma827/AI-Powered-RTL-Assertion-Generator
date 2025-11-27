"""
Example RTL Designs v9.3.1
Complete collection of Verilog/SystemVerilog examples
"""

# ============================================
# ADDERS
# ============================================

HALF_ADDER_BEHAVIORAL = """
module half_adder (
    input  logic a,
    input  logic b,
    output logic sum,
    output logic carry
);
    always_comb begin
        sum = a ^ b;
        carry = a & b;
    end
endmodule
"""

HALF_ADDER_DATAFLOW = """
module half_adder (
    input  logic a,
    input  logic b,
    output logic sum,
    output logic carry
);
    assign sum = a ^ b;
    assign carry = a & b;
endmodule
"""

HALF_ADDER_STRUCTURAL = """
module half_adder (
    input  logic a,
    input  logic b,
    output logic sum,
    output logic carry
);
    xor u1 (sum, a, b);
    and u2 (carry, a, b);
endmodule
"""

FULL_ADDER_BEHAVIORAL = """
module full_adder (
    input  logic a,
    input  logic b,
    input  logic cin,
    output logic sum,
    output logic cout
);
    always_comb begin
        sum = a ^ b ^ cin;
        cout = (a & b) | (b & cin) | (a & cin);
    end
endmodule
"""

FULL_ADDER_DATAFLOW = """
module full_adder (
    input  logic a,
    input  logic b,
    input  logic cin,
    output logic sum,
    output logic cout
);
    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (b & cin) | (a & cin);
endmodule
"""

FULL_ADDER_STRUCTURAL = """
module full_adder (
    input  logic a,
    input  logic b,
    input  logic cin,
    output logic sum,
    output logic cout
);
    wire w1, w2, w3;
    
    xor u1 (w1, a, b);
    xor u2 (sum, w1, cin);
    and u3 (w2, a, b);
    and u4 (w3, w1, cin);
    or  u5 (cout, w2, w3);
endmodule
"""

# ============================================
# MULTIPLEXERS
# ============================================

MUX_2TO1_BEHAVIORAL = """
module mux_2to1 (
    input  logic [7:0] d0,
    input  logic [7:0] d1,
    input  logic       sel,
    output logic [7:0] y
);
    always_comb begin
        if (sel)
            y = d1;
        else
            y = d0;
    end
endmodule
"""

MUX_2TO1_DATAFLOW = """
module mux_2to1 (
    input  logic [7:0] d0,
    input  logic [7:0] d1,
    input  logic       sel,
    output logic [7:0] y
);
    assign y = sel ? d1 : d0;
endmodule
"""

MUX_4TO1_BEHAVIORAL = """
module mux_4to1 (
    input  logic [7:0] d0,
    input  logic [7:0] d1,
    input  logic [7:0] d2,
    input  logic [7:0] d3,
    input  logic [1:0] sel,
    output logic [7:0] y
);
    always_comb begin
        case (sel)
            2'b00: y = d0;
            2'b01: y = d1;
            2'b10: y = d2;
            2'b11: y = d3;
        endcase
    end
endmodule
"""

MUX_4TO1_DATAFLOW = """
module mux_4to1 (
    input  logic [7:0] d0,
    input  logic [7:0] d1,
    input  logic [7:0] d2,
    input  logic [7:0] d3,
    input  logic [1:0] sel,
    output logic [7:0] y
);
    assign y = (sel == 2'b00) ? d0 :
               (sel == 2'b01) ? d1 :
               (sel == 2'b10) ? d2 : d3;
endmodule
"""

# ============================================
# DEMULTIPLEXERS
# ============================================

DEMUX_1TO2_BEHAVIORAL = """
module demux_1to2 (
    input  logic [7:0] d,
    input  logic       sel,
    output logic [7:0] y0,
    output logic [7:0] y1
);
    always_comb begin
        y0 = 8'b0;
        y1 = 8'b0;
        if (sel)
            y1 = d;
        else
            y0 = d;
    end
endmodule
"""

DEMUX_1TO4_BEHAVIORAL = """
module demux_1to4 (
    input  logic [7:0] d,
    input  logic [1:0] sel,
    output logic [7:0] y0,
    output logic [7:0] y1,
    output logic [7:0] y2,
    output logic [7:0] y3
);
    always_comb begin
        y0 = 8'b0;
        y1 = 8'b0;
        y2 = 8'b0;
        y3 = 8'b0;
        case (sel)
            2'b00: y0 = d;
            2'b01: y1 = d;
            2'b10: y2 = d;
            2'b11: y3 = d;
        endcase
    end
endmodule
"""

DEMUX_1TO4_DATAFLOW = """
module demux_1to4 (
    input  logic [7:0] d,
    input  logic [1:0] sel,
    output logic [7:0] y0,
    output logic [7:0] y1,
    output logic [7:0] y2,
    output logic [7:0] y3
);
    assign y0 = (sel == 2'b00) ? d : 8'b0;
    assign y1 = (sel == 2'b01) ? d : 8'b0;
    assign y2 = (sel == 2'b10) ? d : 8'b0;
    assign y3 = (sel == 2'b11) ? d : 8'b0;
endmodule
"""

# ============================================
# ENCODERS
# ============================================

ENCODER_4TO2 = """
module encoder_4to2 (
    input  logic [3:0] in,
    output logic [1:0] out,
    output logic       valid
);
    always_comb begin
        valid = |in;
        casez (in)
            4'b1???: out = 2'b11;
            4'b01??: out = 2'b10;
            4'b001?: out = 2'b01;
            4'b0001: out = 2'b00;
            default: out = 2'b00;
        endcase
    end
endmodule
"""

ENCODER_8TO3 = """
module encoder_8to3 (
    input  logic [7:0] in,
    output logic [2:0] out,
    output logic       valid
);
    always_comb begin
        valid = |in;
        casez (in)
            8'b1???????: out = 3'b111;
            8'b01??????: out = 3'b110;
            8'b001?????: out = 3'b101;
            8'b0001????: out = 3'b100;
            8'b00001???: out = 3'b011;
            8'b000001??: out = 3'b010;
            8'b0000001?: out = 3'b001;
            8'b00000001: out = 3'b000;
            default:     out = 3'b000;
        endcase
    end
endmodule
"""

# ============================================
# DECODERS
# ============================================

DECODER_2TO4_BEHAVIORAL = """
module decoder_2to4 (
    input  logic [1:0] in,
    input  logic       en,
    output logic [3:0] out
);
    always_comb begin
        out = 4'b0000;
        if (en) begin
            case (in)
                2'b00: out = 4'b0001;
                2'b01: out = 4'b0010;
                2'b10: out = 4'b0100;
                2'b11: out = 4'b1000;
            endcase
        end
    end
endmodule
"""

DECODER_2TO4_DATAFLOW = """
module decoder_2to4 (
    input  logic [1:0] in,
    input  logic       en,
    output logic [3:0] out
);
    assign out = en ? (4'b0001 << in) : 4'b0000;
endmodule
"""

DECODER_3TO8 = """
module decoder_3to8 (
    input  logic [2:0] in,
    input  logic       en,
    output logic [7:0] out
);
    always_comb begin
        out = 8'b00000000;
        if (en) begin
            out = 8'b00000001 << in;
        end
    end
endmodule
"""

# ============================================
# COUNTERS
# ============================================

COUNTER_UP = """
module counter_up #(
    parameter WIDTH = 8
)(
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    output logic [WIDTH-1:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= '0;
        else if (en)
            count <= count + 1'b1;
    end
endmodule
"""

COUNTER_DOWN = """
module counter_down #(
    parameter WIDTH = 8
)(
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    output logic [WIDTH-1:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= {WIDTH{1'b1}};
        else if (en)
            count <= count - 1'b1;
    end
endmodule
"""

COUNTER_UPDOWN = """
module counter_updown #(
    parameter WIDTH = 8
)(
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    input  logic             up_down,
    output logic [WIDTH-1:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= '0;
        else if (en) begin
            if (up_down)
                count <= count + 1'b1;
            else
                count <= count - 1'b1;
        end
    end
endmodule
"""

COUNTER_MOD10 = """
module counter_mod10 (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       en,
    output logic [3:0] count,
    output logic       tc
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 4'b0000;
        else if (en) begin
            if (count == 4'd9)
                count <= 4'b0000;
            else
                count <= count + 1'b1;
        end
    end
    
    assign tc = (count == 4'd9) & en;
endmodule
"""

# ============================================
# FSM
# ============================================

FSM_SIMPLE = """
module fsm_simple (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       start,
    input  logic       done,
    output logic       busy,
    output logic       ready,
    output logic [1:0] state
);
    typedef enum logic [1:0] {
        IDLE    = 2'b00,
        RUNNING = 2'b01,
        DONE    = 2'b10
    } state_t;
    
    state_t current_state, next_state;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= IDLE;
        else
            current_state <= next_state;
    end
    
    always_comb begin
        next_state = current_state;
        case (current_state)
            IDLE:    if (start) next_state = RUNNING;
            RUNNING: if (done)  next_state = DONE;
            DONE:    next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end
    
    assign busy  = (current_state == RUNNING);
    assign ready = (current_state == IDLE);
    assign state = current_state;
endmodule
"""

# ============================================
# FREQUENCY DIVIDERS
# ============================================

FREQ_DIV_BY2 = """
module freq_div_by2 (
    input  logic clk,
    input  logic rst_n,
    output logic clk_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            clk_out <= 1'b0;
        else
            clk_out <= ~clk_out;
    end
endmodule
"""

FREQ_DIV_BY_N = """
module freq_div_by_n #(
    parameter N = 10
)(
    input  logic clk,
    input  logic rst_n,
    output logic clk_out
);
    localparam WIDTH = $clog2(N);
    logic [WIDTH-1:0] count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= '0;
            clk_out <= 1'b0;
        end else begin
            if (count == N/2 - 1) begin
                count <= '0;
                clk_out <= ~clk_out;
            end else begin
                count <= count + 1'b1;
            end
        end
    end
endmodule
"""

# ============================================
# COMPARATORS
# ============================================

COMPARATOR_1BIT_BEHAVIORAL = """
module comparator_1bit (
    input  logic a,
    input  logic b,
    output logic eq,
    output logic gt,
    output logic lt
);
    always_comb begin
        eq = (a == b);
        gt = (a > b);
        lt = (a < b);
    end
endmodule
"""

COMPARATOR_1BIT_DATAFLOW = """
module comparator_1bit (
    input  logic a,
    input  logic b,
    output logic eq,
    output logic gt,
    output logic lt
);
    assign eq = ~(a ^ b);
    assign gt = a & ~b;
    assign lt = ~a & b;
endmodule
"""

COMPARATOR_4BIT = """
module comparator_4bit (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic       eq,
    output logic       gt,
    output logic       lt
);
    always_comb begin
        eq = (a == b);
        gt = (a > b);
        lt = (a < b);
    end
endmodule
"""

COMPARATOR_NBIT_BEHAVIORAL = """
module comparator_nbit #(
    parameter WIDTH = 8
)(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic             eq,
    output logic             gt,
    output logic             lt
);
    always_comb begin
        eq = (a == b);
        gt = (a > b);
        lt = (a < b);
    end
endmodule
"""

COMPARATOR_NBIT_DATAFLOW = """
module comparator_nbit #(
    parameter WIDTH = 8
)(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic             eq,
    output logic             gt,
    output logic             lt
);
    assign eq = (a == b);
    assign gt = (a > b);
    assign lt = (a < b);
endmodule
"""

# ============================================
# MEMORY & BUFFERS
# ============================================

FIFO_SYNC = """
module fifo_sync #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
)(
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    wr_en,
    input  logic                    rd_en,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic [DATA_WIDTH-1:0]   rd_data,
    output logic                    full,
    output logic                    empty,
    output logic [$clog2(DEPTH):0]  count
);
    localparam PTR_WIDTH = $clog2(DEPTH);
    
    logic [DATA_WIDTH-1:0] mem [DEPTH-1:0];
    logic [PTR_WIDTH-1:0]  wr_ptr, rd_ptr;
    logic [PTR_WIDTH:0]    fifo_count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            wr_ptr <= '0;
        else if (wr_en && !full) begin
            mem[wr_ptr] <= wr_data;
            wr_ptr <= wr_ptr + 1'b1;
        end
    end
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rd_ptr <= '0;
        else if (rd_en && !empty)
            rd_ptr <= rd_ptr + 1'b1;
    end
    
    assign rd_data = mem[rd_ptr];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            fifo_count <= '0;
        else begin
            case ({wr_en && !full, rd_en && !empty})
                2'b10:   fifo_count <= fifo_count + 1'b1;
                2'b01:   fifo_count <= fifo_count - 1'b1;
                default: fifo_count <= fifo_count;
            endcase
        end
    end
    
    assign full  = (fifo_count == DEPTH);
    assign empty = (fifo_count == 0);
    assign count = fifo_count;
endmodule
"""

FIFO_ASYNC = """
module fifo_async #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
)(
    input  logic                    wr_clk,
    input  logic                    wr_rst_n,
    input  logic                    wr_en,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    output logic                    full,
    
    input  logic                    rd_clk,
    input  logic                    rd_rst_n,
    input  logic                    rd_en,
    output logic [DATA_WIDTH-1:0]   rd_data,
    output logic                    empty
);
    localparam PTR_WIDTH = $clog2(DEPTH);
    
    logic [DATA_WIDTH-1:0] mem [DEPTH-1:0];
    logic [PTR_WIDTH:0]    wr_ptr, rd_ptr;
    logic [PTR_WIDTH:0]    wr_ptr_gray, rd_ptr_gray;
    logic [PTR_WIDTH:0]    wr_ptr_gray_sync, rd_ptr_gray_sync;
    
    function logic [PTR_WIDTH:0] bin2gray(input logic [PTR_WIDTH:0] bin);
        return bin ^ (bin >> 1);
    endfunction
    
    always_ff @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) begin
            wr_ptr <= '0;
            wr_ptr_gray <= '0;
        end else if (wr_en && !full) begin
            wr_ptr <= wr_ptr + 1'b1;
            wr_ptr_gray <= bin2gray(wr_ptr + 1'b1);
            mem[wr_ptr[PTR_WIDTH-1:0]] <= wr_data;
        end
    end
    
    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n) begin
            rd_ptr <= '0;
            rd_ptr_gray <= '0;
        end else if (rd_en && !empty) begin
            rd_ptr <= rd_ptr + 1'b1;
            rd_ptr_gray <= bin2gray(rd_ptr + 1'b1);
        end
    end
    
    assign rd_data = mem[rd_ptr[PTR_WIDTH-1:0]];
    
    always_ff @(posedge wr_clk) rd_ptr_gray_sync <= rd_ptr_gray;
    always_ff @(posedge rd_clk) wr_ptr_gray_sync <= wr_ptr_gray;
    
    assign full  = (wr_ptr_gray == {~rd_ptr_gray_sync[PTR_WIDTH:PTR_WIDTH-1], rd_ptr_gray_sync[PTR_WIDTH-2:0]});
    assign empty = (rd_ptr_gray == wr_ptr_gray_sync);
endmodule
"""

REGISTER_FILE = """
module register_file #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 5,
    parameter NUM_REGS = 32
)(
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    wr_en,
    input  logic [ADDR_WIDTH-1:0]   wr_addr,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    input  logic [ADDR_WIDTH-1:0]   rd_addr1,
    output logic [DATA_WIDTH-1:0]   rd_data1,
    input  logic [ADDR_WIDTH-1:0]   rd_addr2,
    output logic [DATA_WIDTH-1:0]   rd_data2
);
    logic [DATA_WIDTH-1:0] regs [NUM_REGS-1:0];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_REGS; i++)
                regs[i] <= '0;
        end else if (wr_en && wr_addr != 0) begin
            regs[wr_addr] <= wr_data;
        end
    end
    
    assign rd_data1 = (rd_addr1 == 0) ? '0 : regs[rd_addr1];
    assign rd_data2 = (rd_addr2 == 0) ? '0 : regs[rd_addr2];
endmodule
"""

# ============================================
# SHIFT REGISTERS
# ============================================

SHIFT_REG_SISO = """
module shift_reg_siso #(
    parameter WIDTH = 8
)(
    input  logic clk,
    input  logic rst_n,
    input  logic en,
    input  logic d_in,
    output logic d_out
);
    logic [WIDTH-1:0] shift_reg;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            shift_reg <= '0;
        else if (en)
            shift_reg <= {shift_reg[WIDTH-2:0], d_in};
    end
    
    assign d_out = shift_reg[WIDTH-1];
endmodule
"""

SHIFT_REG_SIPO = """
module shift_reg_sipo #(
    parameter WIDTH = 8
)(
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    input  logic             d_in,
    output logic [WIDTH-1:0] d_out
);
    logic [WIDTH-1:0] shift_reg;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            shift_reg <= '0;
        else if (en)
            shift_reg <= {shift_reg[WIDTH-2:0], d_in};
    end
    
    assign d_out = shift_reg;
endmodule
"""

SHIFT_REG_PISO = """
module shift_reg_piso #(
    parameter WIDTH = 8
)(
    input  logic             clk,
    input  logic             rst_n,
    input  logic             load,
    input  logic             shift_en,
    input  logic [WIDTH-1:0] d_in,
    output logic             d_out
);
    logic [WIDTH-1:0] shift_reg;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            shift_reg <= '0;
        else if (load)
            shift_reg <= d_in;
        else if (shift_en)
            shift_reg <= {1'b0, shift_reg[WIDTH-1:1]};
    end
    
    assign d_out = shift_reg[0];
endmodule
"""

SHIFT_REG_PIPO = """
module shift_reg_pipo #(
    parameter WIDTH = 8
)(
    input  logic             clk,
    input  logic             rst_n,
    input  logic             load,
    input  logic [WIDTH-1:0] d_in,
    output logic [WIDTH-1:0] d_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            d_out <= '0;
        else if (load)
            d_out <= d_in;
    end
endmodule
"""

# ============================================
# ARITHMETIC UNITS
# ============================================

ALU_8BIT = """
module alu_8bit (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [3:0] op,
    output logic [7:0] result,
    output logic       zero,
    output logic       carry,
    output logic       overflow
);
    logic [8:0] temp;
    
    always_comb begin
        temp = 9'b0;
        result = 8'b0;
        carry = 1'b0;
        overflow = 1'b0;
        
        case (op)
            4'b0000: temp = a + b;           // ADD
            4'b0001: temp = a - b;           // SUB
            4'b0010: result = a & b;         // AND
            4'b0011: result = a | b;         // OR
            4'b0100: result = a ^ b;         // XOR
            4'b0101: result = ~a;            // NOT
            4'b0110: result = a << 1;        // SHL
            4'b0111: result = a >> 1;        // SHR
            4'b1000: result = {a[6:0], a[7]};// ROL
            4'b1001: result = {a[0], a[7:1]};// ROR
            4'b1010: temp = a + 1;           // INC
            4'b1011: temp = a - 1;           // DEC
            default: result = 8'b0;
        endcase
        
        if (op inside {4'b0000, 4'b0001, 4'b1010, 4'b1011}) begin
            result = temp[7:0];
            carry = temp[8];
            overflow = (a[7] == b[7]) && (result[7] != a[7]);
        end
    end
    
    assign zero = (result == 8'b0);
endmodule
"""

MULTIPLIER = """
module multiplier #(
    parameter WIDTH = 8
)(
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic                 start,
    input  logic [WIDTH-1:0]     a,
    input  logic [WIDTH-1:0]     b,
    output logic [2*WIDTH-1:0]   product,
    output logic                 done
);
    typedef enum logic [1:0] {IDLE, MULTIPLY, COMPLETE} state_t;
    state_t state;
    
    logic [WIDTH-1:0] multiplicand;
    logic [WIDTH-1:0] multiplier_reg;
    logic [2*WIDTH-1:0] result;
    logic [$clog2(WIDTH):0] count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            product <= '0;
            done <= 1'b0;
            count <= '0;
        end else begin
            case (state)
                IDLE: begin
                    done <= 1'b0;
                    if (start) begin
                        multiplicand <= a;
                        multiplier_reg <= b;
                        result <= '0;
                        count <= '0;
                        state <= MULTIPLY;
                    end
                end
                
                MULTIPLY: begin
                    if (multiplier_reg[0])
                        result <= result + (multiplicand << count);
                    multiplier_reg <= multiplier_reg >> 1;
                    count <= count + 1;
                    if (count == WIDTH - 1)
                        state <= COMPLETE;
                end
                
                COMPLETE: begin
                    product <= result;
                    done <= 1'b1;
                    state <= IDLE;
                end
            endcase
        end
    end
endmodule
"""

DIVIDER = """
module divider #(
    parameter WIDTH = 8
)(
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic                 start,
    input  logic [WIDTH-1:0]     dividend,
    input  logic [WIDTH-1:0]     divisor,
    output logic [WIDTH-1:0]     quotient,
    output logic [WIDTH-1:0]     remainder,
    output logic                 done,
    output logic                 div_by_zero
);
    typedef enum logic [1:0] {IDLE, DIVIDE, COMPLETE} state_t;
    state_t state;
    
    logic [WIDTH-1:0] dividend_reg;
    logic [WIDTH-1:0] divisor_reg;
    logic [WIDTH-1:0] quotient_reg;
    logic [WIDTH:0] remainder_reg;
    logic [$clog2(WIDTH):0] count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            quotient <= '0;
            remainder <= '0;
            done <= 1'b0;
            div_by_zero <= 1'b0;
        end else begin
            case (state)
                IDLE: begin
                    done <= 1'b0;
                    div_by_zero <= 1'b0;
                    if (start) begin
                        if (divisor == 0) begin
                            div_by_zero <= 1'b1;
                            done <= 1'b1;
                        end else begin
                            dividend_reg <= dividend;
                            divisor_reg <= divisor;
                            quotient_reg <= '0;
                            remainder_reg <= '0;
                            count <= WIDTH;
                            state <= DIVIDE;
                        end
                    end
                end
                
                DIVIDE: begin
                    remainder_reg <= {remainder_reg[WIDTH-1:0], dividend_reg[WIDTH-1]};
                    dividend_reg <= dividend_reg << 1;
                    
                    if ({remainder_reg[WIDTH-1:0], dividend_reg[WIDTH-1]} >= divisor_reg) begin
                        remainder_reg <= {remainder_reg[WIDTH-1:0], dividend_reg[WIDTH-1]} - divisor_reg;
                        quotient_reg <= {quotient_reg[WIDTH-2:0], 1'b1};
                    end else begin
                        quotient_reg <= {quotient_reg[WIDTH-2:0], 1'b0};
                    end
                    
                    count <= count - 1;
                    if (count == 1)
                        state <= COMPLETE;
                end
                
                COMPLETE: begin
                    quotient <= quotient_reg;
                    remainder <= remainder_reg[WIDTH-1:0];
                    done <= 1'b1;
                    state <= IDLE;
                end
            endcase
        end
    end
endmodule
"""

# ============================================
# EXAMPLES DICTIONARY
# ============================================

EXAMPLES = {
    # Adders
    "half_adder_behavioral": HALF_ADDER_BEHAVIORAL,
    "half_adder_dataflow": HALF_ADDER_DATAFLOW,
    "half_adder_structural": HALF_ADDER_STRUCTURAL,
    "full_adder_behavioral": FULL_ADDER_BEHAVIORAL,
    "full_adder_dataflow": FULL_ADDER_DATAFLOW,
    "full_adder_structural": FULL_ADDER_STRUCTURAL,
    
    # Multiplexers
    "mux_2to1_behavioral": MUX_2TO1_BEHAVIORAL,
    "mux_2to1_dataflow": MUX_2TO1_DATAFLOW,
    "mux_4to1_behavioral": MUX_4TO1_BEHAVIORAL,
    "mux_4to1_dataflow": MUX_4TO1_DATAFLOW,
    
    # Demultiplexers
    "demux_1to2_behavioral": DEMUX_1TO2_BEHAVIORAL,
    "demux_1to4_behavioral": DEMUX_1TO4_BEHAVIORAL,
    "demux_1to4_dataflow": DEMUX_1TO4_DATAFLOW,
    
    # Encoders
    "encoder_4to2": ENCODER_4TO2,
    "encoder_8to3": ENCODER_8TO3,
    
    # Decoders
    "decoder_2to4_behavioral": DECODER_2TO4_BEHAVIORAL,
    "decoder_2to4_dataflow": DECODER_2TO4_DATAFLOW,
    "decoder_3to8": DECODER_3TO8,
    
    # Counters
    "counter_up": COUNTER_UP,
    "counter_down": COUNTER_DOWN,
    "counter_updown": COUNTER_UPDOWN,
    "counter_mod10": COUNTER_MOD10,
    
    # FSM
    "fsm_simple": FSM_SIMPLE,
    
    # Frequency Dividers
    "freq_div_by2": FREQ_DIV_BY2,
    "freq_div_by_n": FREQ_DIV_BY_N,
    
    # Comparators
    "comparator_1bit_behavioral": COMPARATOR_1BIT_BEHAVIORAL,
    "comparator_1bit_dataflow": COMPARATOR_1BIT_DATAFLOW,
    "comparator_4bit": COMPARATOR_4BIT,
    "comparator_nbit_behavioral": COMPARATOR_NBIT_BEHAVIORAL,
    "comparator_nbit_dataflow": COMPARATOR_NBIT_DATAFLOW,
    
    # Memory & Buffers
    "fifo_sync": FIFO_SYNC,
    "fifo_async": FIFO_ASYNC,
    "register_file": REGISTER_FILE,
    
    # Shift Registers
    "shift_reg_siso": SHIFT_REG_SISO,
    "shift_reg_sipo": SHIFT_REG_SIPO,
    "shift_reg_piso": SHIFT_REG_PISO,
    "shift_reg_pipo": SHIFT_REG_PIPO,
    
    # Arithmetic Units
    "alu_8bit": ALU_8BIT,
    "multiplier": MULTIPLIER,
    "divider": DIVIDER,
}


def get_example_designs():
    """Return categorized list of all available examples"""
    return {
        "Combinational Logic": {
            "Half Adder": ["half_adder_behavioral", "half_adder_dataflow", "half_adder_structural"],
            "Full Adder": ["full_adder_behavioral", "full_adder_dataflow", "full_adder_structural"],
            "2:1 MUX": ["mux_2to1_behavioral", "mux_2to1_dataflow"],
            "4:1 MUX": ["mux_4to1_behavioral", "mux_4to1_dataflow"],
            "1:2 DEMUX": ["demux_1to2_behavioral"],
            "1:4 DEMUX": ["demux_1to4_behavioral", "demux_1to4_dataflow"]
        },
        "Encoders & Decoders": {
            "4:2 Encoder": ["encoder_4to2"],
            "8:3 Encoder": ["encoder_8to3"],
            "2:4 Decoder": ["decoder_2to4_behavioral", "decoder_2to4_dataflow"],
            "3:8 Decoder": ["decoder_3to8"]
        },
        "Sequential Logic": {
            "Up Counter": ["counter_up"],
            "Down Counter": ["counter_down"],
            "Up/Down Counter": ["counter_updown"],
            "BCD Counter": ["counter_mod10"],
            "Simple FSM": ["fsm_simple"]
        },
        "Frequency Dividers": {
            "Divide by 2": ["freq_div_by2"],
            "Divide by N": ["freq_div_by_n"]
        },
        "Comparators": {
            "1-bit": ["comparator_1bit_behavioral", "comparator_1bit_dataflow"],
            "4-bit": ["comparator_4bit"],
            "N-bit": ["comparator_nbit_behavioral", "comparator_nbit_dataflow"]
        },
        "Memory & Buffers": {
            "Sync FIFO": ["fifo_sync"],
            "Async FIFO": ["fifo_async"],
            "Register File": ["register_file"]
        },
        "Shift Registers": {
            "SISO": ["shift_reg_siso"],
            "SIPO": ["shift_reg_sipo"],
            "PISO": ["shift_reg_piso"],
            "PIPO": ["shift_reg_pipo"]
        },
        "Arithmetic Units": {
            "ALU (8-bit)": ["alu_8bit"],
            "Multiplier": ["multiplier"],
            "Divider": ["divider"]
        }
    }


def get_example_code(name: str) -> str:
    """Get example code by name"""
    return EXAMPLES.get(name, "")
