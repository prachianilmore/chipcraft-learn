import { useParams, useNavigate } from "react-router-dom";
import { Button } from "@/components/ui/button";
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { Separator } from "@/components/ui/separator";
import { ArrowLeft, ExternalLink, Code, FileText, HelpCircle } from "lucide-react";

const ModuleDetail = () => {
  const { slug } = useParams();
  const navigate = useNavigate();

  // Module data - Verilog Fundamentals Track
  const modulesData: Record<string, any> = {
    "verilog-01-basics-syntax": {
      id: "VF-01",
      title: "Verilog 01 – Basics & Syntax",
      description: "Learn fundamental Verilog syntax, module structure, and basic operators",
      difficulty: "Beginner",
      topics: ["Module Declaration", "Data Types", "Operators", "Basic Syntax"],
      concept: `Verilog is a Hardware Description Language (HDL) used to model digital circuits. Unlike software programming, Verilog describes hardware that operates in parallel.

**Key Concepts:**
- **Modules**: The basic building block in Verilog. Every design starts with a module.
- **Ports**: Interfaces to the outside world (input, output, inout)
- **Data Types**: wire (for combinational) and reg (for sequential/procedural)
- **Operators**: Similar to C (& | ^ ~ + - * / == != < >)`,
      keySyntax: `// Module declaration
module module_name (
  input wire [3:0] in_signal,
  output wire [3:0] out_signal
);
  // Logic here
endmodule

// Basic operators
assign result = a & b;      // AND
assign result = a | b;      // OR
assign result = a ^ b;      // XOR
assign result = ~a;         // NOT
assign result = a + b;      // Addition`,
      exampleCode: `// Example 1: Simple AND gate
module and_gate (
  input wire a,
  input wire b,
  output wire y
);
  assign y = a & b;
endmodule

// Example 2: 4-bit adder
module adder_4bit (
  input wire [3:0] a,
  input wire [3:0] b,
  output wire [3:0] sum,
  output wire carry_out
);
  assign {carry_out, sum} = a + b;
endmodule`,
      expectedOutput: `For the AND gate:
- When a=0, b=0 → y=0
- When a=0, b=1 → y=0
- When a=1, b=0 → y=0
- When a=1, b=1 → y=1

For the 4-bit adder:
- Input: a=0101 (5), b=0011 (3) → sum=1000 (8), carry_out=0
- Input: a=1111 (15), b=0001 (1) → sum=0000 (0), carry_out=1`,
      quiz: [
        { question: "What is the basic building block in Verilog?", answer: "Module" },
        { question: "Which data type is used for combinational logic?", answer: "wire" },
        { question: "What keyword is used for continuous assignment?", answer: "assign" },
        { question: "What does the ^ operator represent?", answer: "XOR (exclusive OR)" },
        { question: "How do you declare a 4-bit input port?", answer: "input wire [3:0] port_name" }
      ]
    },
    "verilog-02-combinational-logic": {
      id: "VF-02",
      title: "Verilog 02 – Combinational Logic",
      description: "Master combinational circuits including gates, multiplexers, and decoders",
      difficulty: "Beginner",
      topics: ["Logic Gates", "assign Statements", "Multiplexers", "Decoders"],
      concept: `Combinational logic circuits produce outputs that depend only on current inputs, with no memory elements.

**Key Concepts:**
- **Gates**: Basic building blocks (AND, OR, NOT, NAND, NOR, XOR)
- **Multiplexers (MUX)**: Select one input from many based on select signal
- **Decoders**: Convert binary input to one-hot output
- **assign Statement**: Used for continuous combinational assignments`,
      keySyntax: `// Continuous assignment
assign output = input1 & input2;

// Conditional operator (ternary)
assign output = sel ? a : b;

// Multiplexer using case
always @(*) begin
  case (sel)
    2'b00: out = in0;
    2'b01: out = in1;
    default: out = 0;
  endcase
end`,
      exampleCode: `// Example 1: 2-to-1 Multiplexer
module mux_2to1 (
  input wire a,
  input wire b,
  input wire sel,
  output wire y
);
  assign y = sel ? b : a;
endmodule

// Example 2: 2-to-4 Decoder
module decoder_2to4 (
  input wire [1:0] in,
  output wire [3:0] out
);
  assign out[0] = ~in[1] & ~in[0];
  assign out[1] = ~in[1] &  in[0];
  assign out[2] =  in[1] & ~in[0];
  assign out[3] =  in[1] &  in[0];
endmodule`,
      expectedOutput: `For 2-to-1 MUX:
- sel=0, a=1, b=0 → y=1 (selects a)
- sel=1, a=1, b=0 → y=0 (selects b)

For 2-to-4 Decoder:
- in=00 → out=0001
- in=01 → out=0010
- in=10 → out=0100
- in=11 → out=1000`,
      quiz: [
        { question: "What is the output of a 2-to-1 MUX when sel=1?", answer: "Input b" },
        { question: "What does a decoder do?", answer: "Converts binary input to one-hot output" },
        { question: "Which operator is used for continuous assignment?", answer: "assign" },
        { question: "What is the conditional operator syntax?", answer: "condition ? true_value : false_value" },
        { question: "Do combinational circuits have memory?", answer: "No, outputs depend only on current inputs" }
      ]
    },
    "verilog-03-sequential-logic": {
      id: "VF-03",
      title: "Verilog 03 – Sequential Logic",
      description: "Understand sequential circuits, flip-flops, and always blocks",
      difficulty: "Beginner",
      topics: ["always Blocks", "Flip-Flops", "Registers", "Clocking"],
      concept: `Sequential logic circuits have memory elements and outputs depend on both current inputs and previous states.

**Key Concepts:**
- **Flip-Flops**: Basic memory element that stores 1 bit
- **Registers**: Groups of flip-flops
- **Clock (clk)**: Synchronizes state changes
- **Reset**: Initializes the circuit to a known state
- **always @(posedge clk)**: Describes synchronous behavior`,
      keySyntax: `// D Flip-Flop with reset
always @(posedge clk or posedge reset) begin
  if (reset)
    q <= 0;
  else
    q <= d;
end

// Important: Use <= for sequential logic (non-blocking)
// Use = for combinational logic in always blocks (blocking)`,
      exampleCode: `// Example 1: D Flip-Flop
module dff (
  input wire clk,
  input wire reset,
  input wire d,
  output reg q
);
  always @(posedge clk or posedge reset) begin
    if (reset)
      q <= 1'b0;
    else
      q <= d;
  end
endmodule

// Example 2: 4-bit Register
module register_4bit (
  input wire clk,
  input wire reset,
  input wire [3:0] d,
  output reg [3:0] q
);
  always @(posedge clk or posedge reset) begin
    if (reset)
      q <= 4'b0000;
    else
      q <= d;
  end
endmodule`,
      expectedOutput: `For D Flip-Flop:
- At reset: q = 0
- At posedge clk: q takes the value of d
- Values are captured on rising clock edge

For 4-bit Register:
- reset=1 → q=0000
- At each clock edge, q captures d value
- Example: d=1010 → after clock edge, q=1010`,
      quiz: [
        { question: "What triggers a flip-flop to update its output?", answer: "Clock edge (posedge or negedge)" },
        { question: "Which assignment operator should be used in sequential always blocks?", answer: "<= (non-blocking)" },
        { question: "What is the purpose of a reset signal?", answer: "To initialize the circuit to a known state" },
        { question: "What does posedge mean?", answer: "Positive edge (0 to 1 transition)" },
        { question: "What keyword is used to declare a variable in sequential logic?", answer: "reg" }
      ]
    },
    "verilog-04-testbenches": {
      id: "VF-04",
      title: "Verilog 04 – Verilog Testbenches",
      description: "Write testbenches to verify your Verilog designs",
      difficulty: "Beginner",
      topics: ["Testbench Structure", "initial Blocks", "Stimulus", "$display"],
      concept: `A testbench is Verilog code that verifies the functionality of your design by applying test inputs and checking outputs.

**Key Concepts:**
- **No ports**: Testbenches are top-level modules with no ports
- **initial block**: Executes once at time 0
- **#delay**: Adds time delay in simulation
- **$display**: Prints values to console
- **$monitor**: Continuously monitors and prints changes
- **$finish**: Ends simulation`,
      keySyntax: `module tb_module_name;
  // Declare signals
  reg input_signal;
  wire output_signal;
  
  // Instantiate DUT (Design Under Test)
  module_name uut (
    .input_port(input_signal),
    .output_port(output_signal)
  );
  
  // Test stimulus
  initial begin
    input_signal = 0;
    #10 input_signal = 1;
    #10 $display("Result: %b", output_signal);
    $finish;
  end
endmodule`,
      exampleCode: `// Design: Simple AND gate
module and_gate (
  input wire a,
  input wire b,
  output wire y
);
  assign y = a & b;
endmodule

// Testbench for AND gate
module tb_and_gate;
  reg a, b;
  wire y;
  
  // Instantiate the AND gate
  and_gate uut (
    .a(a),
    .b(b),
    .y(y)
  );
  
  // Test stimulus
  initial begin
    $display("Testing AND Gate");
    $display("Time\\ta\\tb\\ty");
    $monitor("%0t\\t%b\\t%b\\t%b", $time, a, b, y);
    
    a = 0; b = 0;
    #10 a = 0; b = 1;
    #10 a = 1; b = 0;
    #10 a = 1; b = 1;
    #10 $finish;
  end
endmodule`,
      expectedOutput: `Testing AND Gate
Time  a  b  y
0     0  0  0
10    0  1  0
20    1  0  0
30    1  1  1

The testbench applies all possible input combinations and displays the results. You can verify that the AND gate behaves correctly.`,
      quiz: [
        { question: "Do testbenches have input/output ports?", answer: "No, testbenches have no ports" },
        { question: "Which block executes once at the start?", answer: "initial block" },
        { question: "What does #10 represent?", answer: "A delay of 10 time units" },
        { question: "What command ends the simulation?", answer: "$finish" },
        { question: "What is DUT?", answer: "Design Under Test (the module being tested)" }
      ]
    },
    "systemverilog-01-from-verilog": {
      id: "SV-01",
      title: "SV 01 – From Verilog to SystemVerilog",
      description: "Understand the key differences and enhancements SystemVerilog brings over Verilog",
      difficulty: "Intermediate",
      topics: ["Enhancements", "New Data Types", "Logic vs Wire/Reg", "Always Constructs"],
      concept: `SystemVerilog is an extension of Verilog that adds powerful features for design, verification, and testbench creation.

**Key Enhancements:**
- **logic type**: Replaces wire/reg confusion with a unified type
- **always_comb/always_ff**: Clearer intent-based always blocks
- **Enhanced data types**: enum, struct, union, typedef
- **Interfaces**: Bundle signals for cleaner connections
- **Assertions**: SVA for property checking`,
      keySyntax: `// Verilog style
reg [7:0] data;
wire [7:0] addr;

// SystemVerilog style (preferred)
logic [7:0] data;
logic [7:0] addr;

// Enum for states
typedef enum logic [1:0] {
  IDLE   = 2'b00,
  ACTIVE = 2'b01,
  DONE   = 2'b10
} state_t;`,
      exampleCode: `// Verilog Style
module mux_verilog (
  input wire [7:0] a,
  input wire [7:0] b,
  input wire sel,
  output reg [7:0] out
);
  always @(*) begin
    if (sel)
      out = b;
    else
      out = a;
  end
endmodule

// SystemVerilog Style
module mux_sv (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic sel,
  output logic [7:0] out
);
  always_comb begin
    out = sel ? b : a;
  end
endmodule`,
      expectedOutput: `Both modules produce identical behavior:
- When sel=0: out = a
- When sel=1: out = b

**Advantages of SystemVerilog:**
- logic eliminates wire/reg confusion
- always_comb clearly indicates combinational intent
- Simulator can check for unintended latches`,
      quiz: [
        { question: "What type replaces both wire and reg in SystemVerilog?", answer: "logic" },
        { question: "What always block should be used for combinational logic?", answer: "always_comb" },
        { question: "What always block should be used for sequential logic?", answer: "always_ff" },
        { question: "Is SystemVerilog backward compatible with Verilog?", answer: "Yes, valid Verilog is valid SystemVerilog" },
        { question: "What feature bundles signals for cleaner connections?", answer: "Interfaces" }
      ]
    },
    "systemverilog-02-types-arrays": {
      id: "SV-02",
      title: "SV 02 – Types, Arrays, and typedef",
      description: "Master SystemVerilog's rich type system including packed/unpacked arrays and typedefs",
      difficulty: "Intermediate",
      topics: ["logic Type", "Packed Arrays", "Unpacked Arrays", "typedef", "enum", "struct"],
      concept: `SystemVerilog provides a rich type system that improves code readability and catches errors at compile time.

**Key Types:**
- **logic**: 4-state type (0, 1, X, Z) for most signals
- **bit**: 2-state type (0, 1) for faster simulation
- **enum**: Enumerated types for state machines
- **struct**: Group related signals
- **typedef**: Create custom type aliases

**Arrays:**
- **Packed**: [7:0] data - stored as continuous bits
- **Unpacked**: data[0:7] - stored as separate elements`,
      keySyntax: `// Typedef for readability
typedef logic [7:0] byte_t;
byte_t data;

// Enum for states
typedef enum logic [1:0] {
  IDLE, FETCH, EXECUTE, WRITEBACK
} state_t;

// Struct for grouping
typedef struct packed {
  logic [7:0] addr;
  logic [31:0] data;
  logic valid;
} transaction_t;`,
      exampleCode: `// Example: State Machine with Enum
module fsm (
  input logic clk,
  input logic reset,
  input logic start,
  output logic done
);
  typedef enum logic [1:0] {
    IDLE    = 2'b00,
    RUNNING = 2'b01,
    FINISH  = 2'b10
  } state_t;
  
  state_t current_state, next_state;
  
  always_ff @(posedge clk or posedge reset) begin
    if (reset)
      current_state <= IDLE;
    else
      current_state <= next_state;
  end
  
  always_comb begin
    next_state = current_state;
    done = 1'b0;
    
    case (current_state)
      IDLE: if (start) next_state = RUNNING;
      RUNNING: next_state = FINISH;
      FINISH: begin
        done = 1'b1;
        next_state = IDLE;
      end
    endcase
  end
endmodule`,
      expectedOutput: `State transitions:
1. Reset → IDLE
2. start=1 → RUNNING (1 cycle)
3. RUNNING → FINISH (1 cycle)
4. FINISH → done=1, return to IDLE

**Benefits:**
- State names are readable (not 2'b00, 2'b01)
- Type checking prevents invalid states
- Easier debugging with state names`,
      quiz: [
        { question: "What's the difference between logic and bit?", answer: "logic is 4-state (0,1,X,Z), bit is 2-state (0,1)" },
        { question: "What keyword creates custom type aliases?", answer: "typedef" },
        { question: "What's the syntax for packed arrays?", answer: "logic [7:0] data" },
        { question: "What type is used for enumerated states?", answer: "enum" },
        { question: "What keyword groups related signals together?", answer: "struct" }
      ]
    },
    "systemverilog-03-always-constructs": {
      id: "SV-03",
      title: "SV 03 – always_comb, always_ff, always_latch",
      description: "Learn SystemVerilog's specialized always blocks for safer RTL coding",
      difficulty: "Intermediate",
      topics: ["always_comb", "always_ff", "always_latch", "Intent vs Implementation"],
      concept: `SystemVerilog introduces specialized always blocks that clearly indicate design intent and help catch common coding errors.

**Three Types:**
- **always_comb**: Combinational logic (no memory)
- **always_ff**: Sequential logic (flip-flops)
- **always_latch**: Latches (rarely used)

**Benefits:**
- Simulator checks for unintended behavior
- Self-documenting code (intent is clear)
- Catches incomplete sensitivity lists
- Prevents accidental latches in always_comb`,
      keySyntax: `// Combinational logic
always_comb begin
  out = a & b;
end

// Sequential logic (flip-flop)
always_ff @(posedge clk) begin
  q <= d;
end

// Explicit latch (rarely needed)
always_latch begin
  if (enable)
    q <= d;
end`,
      exampleCode: `// Example 1: Combinational Logic
module decoder (
  input logic [1:0] sel,
  output logic [3:0] out
);
  always_comb begin
    out = 4'b0000;
    case (sel)
      2'b00: out = 4'b0001;
      2'b01: out = 4'b0010;
      2'b10: out = 4'b0100;
      2'b11: out = 4'b1000;
    endcase
  end
endmodule

// Example 2: Sequential Logic
module counter (
  input logic clk,
  input logic reset,
  input logic enable,
  output logic [3:0] count
);
  always_ff @(posedge clk or posedge reset) begin
    if (reset)
      count <= 4'b0000;
    else if (enable)
      count <= count + 1;
  end
endmodule`,
      expectedOutput: `Decoder output for each input:
- sel=00 → out=0001
- sel=01 → out=0010
- sel=10 → out=0100
- sel=11 → out=1000

Counter behavior:
- reset=1 → count=0
- enable=1 → count increments each clock
- enable=0 → count holds

**Advantage:** Simulator warns if always_comb accidentally creates a latch`,
      quiz: [
        { question: "Which always block is used for combinational logic?", answer: "always_comb" },
        { question: "Which always block is used for flip-flops?", answer: "always_ff" },
        { question: "What does always_comb prevent?", answer: "Unintended latches" },
        { question: "Can always_comb have a sensitivity list?", answer: "No, it's implicit and automatic" },
        { question: "Which always block requires a clock edge?", answer: "always_ff" }
      ]
    },
    "systemverilog-04-interfaces": {
      id: "SV-04",
      title: "SV 04 – Interfaces & Modports",
      description: "Simplify module connections with SystemVerilog interfaces and modports",
      difficulty: "Intermediate",
      topics: ["interface", "modport", "Bundle Signals", "Design Hierarchy"],
      concept: `Interfaces bundle related signals together, reducing connection errors and improving code maintainability.

**Key Concepts:**
- **interface**: Groups signals that logically belong together
- **modport**: Defines directional views (master/slave, input/output)
- **Benefits**: Less code, fewer errors, easier refactoring

**Use Cases:**
- Bus protocols (AXI, AHB, APB)
- Memory interfaces
- Any multi-signal connection between modules`,
      keySyntax: `// Define interface
interface bus_if;
  logic [7:0] addr;
  logic [31:0] data;
  logic valid;
  logic ready;
  
  modport master (
    output addr, data, valid,
    input ready
  );
  
  modport slave (
    input addr, data, valid,
    output ready
  );
endinterface`,
      exampleCode: `// Interface definition
interface simple_bus;
  logic [7:0] addr;
  logic [7:0] data;
  logic valid;
  
  modport master (output addr, data, valid);
  modport slave (input addr, data, valid);
endinterface

// Master module
module master (
  input logic clk,
  simple_bus.master bus
);
  always_ff @(posedge clk) begin
    bus.addr <= bus.addr + 1;
    bus.data <= bus.addr * 2;
    bus.valid <= 1'b1;
  end
endmodule

// Slave module
module slave (
  input logic clk,
  simple_bus.slave bus
);
  always_ff @(posedge clk) begin
    if (bus.valid)
      $display("Received: addr=%h data=%h", 
               bus.addr, bus.data);
  end
endmodule

// Top-level connection
module top;
  logic clk;
  simple_bus bus_inst();
  
  master m1 (.clk(clk), .bus(bus_inst));
  slave s1 (.clk(clk), .bus(bus_inst));
endmodule`,
      expectedOutput: `Without interfaces, you'd need:
  master m1 (.addr(addr), .data(data), .valid(valid));
  slave s1 (.addr(addr), .data(data), .valid(valid));

With interfaces:
  master m1 (.bus(bus_inst));
  slave s1 (.bus(bus_inst));

**Benefits:**
- Single connection instead of multiple wires
- Modport enforces correct directionality
- Easy to add/remove signals
- Less error-prone`,
      quiz: [
        { question: "What does an interface bundle together?", answer: "Related signals" },
        { question: "What defines directional views in an interface?", answer: "modport" },
        { question: "Can you have multiple modports in one interface?", answer: "Yes, e.g., master and slave" },
        { question: "What's a common use case for interfaces?", answer: "Bus protocols and memory interfaces" },
        { question: "How does an interface reduce errors?", answer: "Bundles signals, enforces direction, reduces manual connections" }
      ]
    },
    "systemverilog-05-sva": {
      id: "SV-05",
      title: "SV 05 – Intro to SVA",
      description: "Introduction to SystemVerilog Assertions for verification and debugging",
      difficulty: "Intermediate",
      topics: ["Assertions", "Properties", "Sequences", "Immediate vs Concurrent"],
      concept: `SystemVerilog Assertions (SVA) enable you to specify and verify design properties, catching bugs early in simulation.

**Two Types:**
- **Immediate assertions**: Check conditions like if-statements (in procedural code)
- **Concurrent assertions**: Check temporal properties over time

**Key Concepts:**
- **assert**: Verify property is true
- **property**: Named assertion rules
- **sequence**: Temporal patterns
- **|->**: Implication operator (if A then B)`,
      keySyntax: `// Immediate assertion
always_comb begin
  assert (data < 256) 
    else $error("Data overflow");
end

// Concurrent assertion
property valid_req;
  @(posedge clk) req |-> ##[1:3] ack;
endproperty

assert property (valid_req)
  else $error("Request not acknowledged");`,
      exampleCode: `// Example: FIFO with Assertions
module fifo_with_sva (
  input logic clk,
  input logic reset,
  input logic push,
  input logic pop,
  input logic [7:0] data_in,
  output logic [7:0] data_out,
  output logic full,
  output logic empty
);
  logic [7:0] mem [0:7];
  logic [2:0] wr_ptr, rd_ptr;
  logic [3:0] count;
  
  // Immediate assertions
  always_comb begin
    assert (count <= 8) 
      else $error("Count overflow");
  end
  
  // Concurrent assertions
  property no_push_when_full;
    @(posedge clk) full |-> !push;
  endproperty
  
  property no_pop_when_empty;
    @(posedge clk) empty |-> !pop;
  endproperty
  
  assert property (no_push_when_full)
    else $error("Push attempted when full");
    
  assert property (no_pop_when_empty)
    else $error("Pop attempted when empty");
  
  // FIFO logic
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      wr_ptr <= 0;
      rd_ptr <= 0;
      count <= 0;
    end else begin
      if (push && !full) begin
        mem[wr_ptr] <= data_in;
        wr_ptr <= wr_ptr + 1;
        count <= count + 1;
      end
      if (pop && !empty) begin
        data_out <= mem[rd_ptr];
        rd_ptr <= rd_ptr + 1;
        count <= count - 1;
      end
    end
  end
  
  assign full = (count == 8);
  assign empty = (count == 0);
endmodule`,
      expectedOutput: `Assertions verify:
1. Count never exceeds 8
2. No push when FIFO is full
3. No pop when FIFO is empty

If violations occur:
- Simulation reports error with message
- Points to exact time and location
- Helps catch bugs during development

**Benefits:**
- Catches illegal operations automatically
- Documents design requirements
- Reduces debug time
- Works in simulation and formal verification`,
      quiz: [
        { question: "What are the two types of assertions?", answer: "Immediate and concurrent" },
        { question: "Where are immediate assertions used?", answer: "In procedural code (always blocks)" },
        { question: "What does |-> mean in SVA?", answer: "Implication (if...then)" },
        { question: "What's the purpose of SVA?", answer: "To verify design properties and catch bugs" },
        { question: "Can assertions be used in formal verification?", answer: "Yes, both simulation and formal tools" }
      ]
    }
  };

  const module = modulesData[slug || "verilog-01-basics-syntax"];

  if (!module) {
    return (
      <div className="min-h-screen py-20 px-4">
        <div className="container mx-auto text-center">
          <h1 className="text-3xl font-bold mb-4">Module Not Found</h1>
          <Button onClick={() => navigate("/modules")}>
            <ArrowLeft className="mr-2" /> Back to Modules
          </Button>
        </div>
      </div>
    );
  }

  const getDifficultyColor = (difficulty: string) => {
    switch (difficulty) {
      case "Beginner":
        return "bg-green-500/10 text-green-600 border-green-500/20";
      case "Intermediate":
        return "bg-highlight/10 text-highlight-foreground border-highlight/20";
      case "Advanced":
        return "bg-destructive/10 text-destructive border-destructive/20";
      default:
        return "bg-muted text-muted-foreground";
    }
  };

  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4 max-w-5xl">
        {/* Header */}
        <Button
          variant="ghost" 
          onClick={() => navigate("/modules")}
          className="mb-6"
        >
          <ArrowLeft className="mr-2" /> Back to Modules
        </Button>

        <div className="mb-8">
          <div className="flex items-center gap-3 mb-4">
            <Badge variant="outline" className="text-xs font-mono">Module {module.id}</Badge>
            <Badge variant="outline" className={getDifficultyColor(module.difficulty)}>
              {module.difficulty}
            </Badge>
          </div>
          <h1 className="text-4xl md:text-5xl font-bold mb-4">{module.title}</h1>
          <p className="text-lg text-muted-foreground">{module.description}</p>
          <div className="flex flex-wrap gap-2 mt-4">
            {module.topics.map((topic: string, index: number) => (
              <Badge key={index} variant="secondary">
                {topic}
              </Badge>
            ))}
          </div>
        </div>

        {/* 1. Concept Summary */}
        <Card className="mb-8">
          <CardHeader>
            <div className="flex items-center gap-2">
              <FileText className="w-5 h-5 text-primary" />
              <CardTitle>Concept Summary</CardTitle>
            </div>
          </CardHeader>
          <CardContent>
            <div className="text-muted-foreground leading-relaxed whitespace-pre-line">{module.concept}</div>
          </CardContent>
        </Card>

        {/* 2. Key Syntax */}
        {module.keySyntax && (
          <Card className="mb-8">
            <CardHeader>
              <div className="flex items-center gap-2">
                <Code className="w-5 h-5 text-primary" />
                <CardTitle>Key Syntax</CardTitle>
              </div>
            </CardHeader>
            <CardContent>
              <pre className="bg-muted p-4 rounded-lg overflow-x-auto">
                <code className="text-sm font-mono">{module.keySyntax}</code>
              </pre>
            </CardContent>
          </Card>
        )}

        {/* 3. Example Code */}
        <Card className="mb-8">
          <CardHeader>
            <div className="flex items-center gap-2">
              <Code className="w-5 h-5 text-primary" />
              <CardTitle>Example Code</CardTitle>
            </div>
            <CardDescription>Verilog implementation</CardDescription>
          </CardHeader>
          <CardContent>
            <pre className="bg-muted p-4 rounded-lg overflow-x-auto">
              <code className="text-sm font-mono">{module.exampleCode}</code>
            </pre>
          </CardContent>
        </Card>

        {/* 4. Run Simulation Button */}
        <Card className="mb-8">
          <CardHeader>
            <CardTitle>Run Simulation</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="flex flex-col sm:flex-row gap-4 items-center justify-between">
              <div>
                <h3 className="font-semibold mb-1">Try it yourself!</h3>
                <p className="text-sm text-muted-foreground">Run this code in EDA Playground</p>
              </div>
              <Button asChild size="lg" className="w-full sm:w-auto">
                <a 
                  href="https://www.edaplayground.com/" 
                  target="_blank" 
                  rel="noopener noreferrer"
                >
                  <ExternalLink className="mr-2" /> Run on EDA Playground
                </a>
              </Button>
            </div>
          </CardContent>
        </Card>

        {/* 5. Expected Output */}
        <Card className="mb-8">
          <CardHeader>
            <CardTitle>Expected Output</CardTitle>
            <CardDescription>What you should see when running the simulation</CardDescription>
          </CardHeader>
          <CardContent>
            <div className="bg-muted p-4 rounded-lg">
              <pre className="text-sm font-mono text-muted-foreground whitespace-pre-line">{module.expectedOutput}</pre>
            </div>
          </CardContent>
        </Card>

        {/* 6. Reflection / Quiz Section */}
        <Card className="mb-8">
          <CardHeader>
            <div className="flex items-center gap-2">
              <HelpCircle className="w-5 h-5 text-primary" />
              <CardTitle>Quiz & Reflection</CardTitle>
            </div>
            <CardDescription>Test your understanding</CardDescription>
          </CardHeader>
          <CardContent className="space-y-6">
            {module.quiz.map((item: any, index: number) => (
              <div key={index} className="border-l-4 border-primary pl-4">
                <h4 className="font-semibold mb-2">Q{index + 1}: {item.question}</h4>
                <details className="text-sm text-muted-foreground">
                  <summary className="cursor-pointer hover:text-foreground transition-colors">
                    Show Answer
                  </summary>
                  <p className="mt-2 pl-4">{item.answer}</p>
                </details>
              </div>
            ))}
          </CardContent>
        </Card>

        <Separator className="my-8" />

        {/* Navigation */}
        <div className="flex justify-between items-center">
          <Button 
            variant="outline" 
            onClick={() => navigate("/modules")}
          >
            <ArrowLeft className="mr-2" /> Back to All Modules
          </Button>
        </div>
      </div>
    </div>
  );
};

export default ModuleDetail;
