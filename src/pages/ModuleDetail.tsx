import { useParams, useNavigate } from "react-router-dom";
import { Button } from "@/components/ui/button";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { Separator } from "@/components/ui/separator";
import { ArrowLeft, Code } from "lucide-react";

const ModuleDetail = () => {
  const { slug } = useParams();
  const navigate = useNavigate();

  // Module data - Verilog Fundamentals Track Only
  const modulesData: Record<string, any> = {
    "verilog-01-basics-syntax": {
      id: "VF-01",
      title: "Verilog 01 – Basics & Syntax",
      description: "Learn fundamental Verilog syntax, module structure, and basic operators",
      difficulty: "Beginner",
      topics: ["Introduction", "Module Structure", "Data Types", "Operators", "Continuous Assignment", "Procedural Blocks", "Control Statements","Example Circuits","Common Beginner Mistakes"],
      Introduction: `Verilog is a Hardware Description Language (HDL) used to model and implement digital logic hardware.It allows designers to describe circuits in terms of behavior, structure, and timing—before silicon is manufactured.This module introduces the essential building blocks of Verilog.`,
      ModuleStructure: [
        "A Verilog design begins with a module, which defines inputs, outputs, internal signals, and logic."],
      Syntax:`module module_name (port_list);
    // Declarations
    // Logic`,

      Example: `module and_gate(input a, input b, output y);
    assign y = a & b;
endmodule
`,
      datatypes: `Commonly Used Types:
- wire: Represents a physical connection; used in combinational logic.
- reg: Holds a value assigned inside an always block.
- integer: Used for loop counters or testbench code.
`,
      vectors:`reg [7:0] data;   // 8-bit data register
wire [3:0] addr;  // 4-bit address bus
`,
      operator:`Bitwise Operators: &, |, ^, ~
Logical Operators: &&, ||, !
Arithmetic Operators: +, -, *
`,
     exampleOperator:`assign y = (a & b) | (~c);`,
     continuousAssignment:`Continuous assignments are used for combinational logic:
assign sum   = a ^ b;
assign carry = a & b;
`,
    proceduralBlocks:`Procedural blocks describe behavior using higher-level logic.`,
    combinationalLogic:`always @(*) begin
    y = a + b;
end
`,
    sequentialLogic:`always @(posedge clk) begin
    q <= d;
end
`, 
    controlStatements:`If–Else and Case statements are used to describe decision logic.`,
    ifElseExample:`always @(*) begin
    if (sel == 0)
        out = a;
    else
        out = b;
end
`,
    caseExample:`always @(*) begin
    case (sel)
        2'b00: out = a;
        2'b01: out = b;
        2'b10: out = c;
        default: out = 0;
    endcase
end
`,
    exampleCircuits:`Below are basic circuits implemented in Verilog.`,
    multiplexer:`assign y = sel ? b : a;
or procedural:
always @(*) begin
    if (sel == 1)
        y = b;
    else
        y = a;
end
`,
     DflipFlop:`module dff(input clk, input d, output reg q);
    always @(posedge clk) begin
        q <= d;
    end
endmodule
`,
     commonBeginnerMistakes:`- Assigning to a wire inside an always block.
- Using = instead of <= in sequential blocks.
- Forgetting @(*) in combinational always blocks.
- Mixing blocking and non-blocking assignments incorrectly.
- Incorrect vector declarations.
`,
},
    "verilog-02-combinational-logic": {
      id: "VF-02",
      title: "Verilog 02 – Combinational Logic",
      description: "Master combinational circuits including gates, multiplexers, and decoders",
      difficulty: "Beginner",
      topics: ["Logic Gates", "assign Statements", "Multiplexers", "Decoders"],
      concept: `Combinational logic circuits produce outputs that depend only on current inputs, with no memory elements. The output changes immediately when inputs change.`,
      keyIdeas: [
        "**Logic Gates** are basic building blocks: AND, OR, NOT, NAND, NOR, XOR, XNOR.",
        "**Multiplexers (MUX)** select one input from many based on a select signal.",
        "**Decoders** convert binary input to one-hot output (only one bit is high).",
        "**assign** statements are used for continuous combinational assignments.",
        "**Conditional operator (?:)** provides simple if-then-else logic: sel ? a : b"
      ],
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
      explanation: `**Multiplexer:** When sel=0, output y follows input a. When sel=1, output y follows input b. This is like a digital switch that routes one of two inputs to the output.

**Decoder:** Converts a 2-bit binary input to a 4-bit one-hot output. For example, input 00 activates out[0], input 01 activates out[1], input 10 activates out[2], and input 11 activates out[3]. Only one output is high at a time.`
    },
    "verilog-03-sequential-logic": {
      id: "VF-03",
      title: "Verilog 03 – Sequential Logic",
      description: "Understand sequential circuits, flip-flops, and always blocks",
      difficulty: "Beginner",
      topics: ["always Blocks", "Flip-Flops", "Registers", "Clocking"],
      concept: `Sequential logic circuits have memory and their outputs depend on both current inputs and previous state. They use clock signals to synchronize state changes.`,
      keyIdeas: [
        "**Flip-Flops** are basic memory elements that store one bit of data.",
        "**Registers** are groups of flip-flops that store multi-bit values.",
        "**Clock (clk)** synchronizes state changes - changes happen on clock edges.",
        "**Reset** initializes the circuit to a known state.",
        "**always @(posedge clk)** describes synchronous behavior (updates on rising clock edge).",
        "**Non-blocking assignment (<=)** should be used in sequential always blocks."
      ],
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

// Example 2: 4-bit Counter
module counter_4bit (
  input wire clk,
  input wire reset,
  output reg [3:0] count
);
  always @(posedge clk or posedge reset) begin
    if (reset)
      count <= 4'b0000;
    else
      count <= count + 1;
  end
endmodule`,
      explanation: `**D Flip-Flop:** Captures the value of input 'd' on the rising edge of the clock. When reset is high, output 'q' is forced to 0. Otherwise, on each clock edge, 'q' takes the value of 'd'.

**4-bit Counter:** Increments by 1 on each rising clock edge. When reset is high, the counter resets to 0. The counter wraps around from 15 (1111) back to 0 (0000). This demonstrates how sequential logic maintains state across clock cycles.`
    },
    "verilog-04-testbenches": {
      id: "VF-04",
      title: "Verilog 04 – Verilog Testbenches",
      description: "Write testbenches to verify your Verilog designs",
      difficulty: "Beginner",
      topics: ["Testbench Structure", "initial Blocks", "Stimulus", "$display"],
      concept: `A testbench is Verilog code that verifies the functionality of your design by applying test inputs and checking outputs. Testbenches are not synthesizable - they're only for simulation.`,
      keyIdeas: [
        "**No ports** - Testbenches are top-level modules with no input/output ports.",
        "**initial block** executes once at time 0 and is used to apply test stimulus.",
        "**#delay** adds time delay in simulation (e.g., #10 means wait 10 time units).",
        "**$display** prints values to the console for verification.",
        "**$monitor** continuously watches and prints signal changes.",
        "**$finish** ends the simulation."
      ],
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
  
  // Instantiate the AND gate (Design Under Test)
  and_gate uut (
    .a(a),
    .b(b),
    .y(y)
  );
  
  // Test stimulus
  initial begin
    $display("Testing AND Gate");
    $display("Time  a  b  y");
    
    a = 0; b = 0; #10;
    $display("%0t    %b  %b  %b", $time, a, b, y);
    
    a = 0; b = 1; #10;
    $display("%0t    %b  %b  %b", $time, a, b, y);
    
    a = 1; b = 0; #10;
    $display("%0t    %b  %b  %b", $time, a, b, y);
    
    a = 1; b = 1; #10;
    $display("%0t    %b  %b  %b", $time, a, b, y);
    
    $finish;
  end
endmodule`,
      explanation: `**Testbench Structure:** The testbench instantiates the design under test (DUT) - in this case, the AND gate. Inputs to the DUT are declared as 'reg' type, and outputs as 'wire' type.

**Test Stimulus:** The initial block applies all four possible input combinations (00, 01, 10, 11) with a 10-time-unit delay between each test. The $display statements show the results: output 'y' should only be 1 when both 'a' and 'b' are 1.

**Expected Output:**
- Time 0: a=0, b=0 → y=0
- Time 10: a=0, b=1 → y=0
- Time 20: a=1, b=0 → y=0
- Time 30: a=1, b=1 → y=1`
    },
    // SystemVerilog Track Modules
    "systemverilog-01-from-verilog": {
      id: "SV-01",
      title: "SystemVerilog 01 – From Verilog to SystemVerilog",
      description: "Understand the key improvements SystemVerilog brings over traditional Verilog",
      difficulty: "Intermediate",
      topics: ["New Features", "Enhanced Syntax", "Data Types", "Logic Type"],
      concept: `SystemVerilog extends Verilog with powerful features for design, verification, and assertion. It maintains backward compatibility while adding modern programming constructs, enhanced data types, and verification-specific capabilities.`,
      keyIdeas: [
        "**logic** type replaces both wire and reg - simplifies variable declarations.",
        "**Enhanced operators**: ++, --, +=, *=, etc. for cleaner code.",
        "**always_comb, always_ff, always_latch** provide intent-specific modeling.",
        "**Interfaces** bundle related signals and simplify connections.",
        "**Classes** enable object-oriented verification environments.",
        "**Backward compatible** - all Verilog code runs in SystemVerilog."
      ],
      exampleCode: `// Example 1: logic vs wire/reg
module counter (
  input  logic       clk,
  input  logic       reset,
  output logic [3:0] count
);
  always_ff @(posedge clk or posedge reset) begin
    if (reset)
      count <= 4'b0;
    else
      count++;  // Enhanced operator
  end
endmodule

// Example 2: Enhanced operators
module accumulator (
  input  logic       clk,
  input  logic [7:0] data_in,
  output logic [7:0] sum
);
  always_ff @(posedge clk) begin
    sum += data_in;  // Cleaner than sum <= sum + data_in
  end
endmodule`,
      explanation: `**logic Type:** Replaces the confusion of wire vs reg. Use 'logic' for all signals except when you need multi-driver nets (use 'wire' with tri-state).

**Enhanced Operators:** The ++ and += operators make code cleaner and match C/C++ syntax. 'count++' is equivalent to 'count <= count + 1'.

**Intent-Specific Always:** always_ff clearly indicates sequential logic with flip-flops, making the code self-documenting and allowing tools to catch mistakes.`
    },
    "systemverilog-02-data-types": {
      id: "SV-02",
      title: "SystemVerilog 02 – Data Types, Arrays, typedef",
      description: "Master SystemVerilog's rich type system",
      difficulty: "Intermediate",
      topics: ["logic vs reg/wire", "Arrays", "typedef", "struct/union"],
      concept: `SystemVerilog provides a rich set of data types beyond Verilog's limited options. These include better integers, packed/unpacked arrays, structures, and user-defined types through typedef.`,
      keyIdeas: [
        "**logic** - 4-state type, use for most hardware signals.",
        "**bit** - 2-state type (0/1 only), faster in simulation, good for testbenches.",
        "**int** - 32-bit signed integer, **byte** - 8-bit signed.",
        "**Packed arrays** [3:0] - stored as continuous bits, can be sliced.",
        "**Unpacked arrays** [4] - separate elements in memory.",
        "**typedef** creates custom type names for reusability.",
        "**struct** groups related data like C structures."
      ],
      exampleCode: `// Example 1: Data types and arrays
module data_types_demo;
  logic [7:0] packed_array;   // 8-bit vector
  logic       unpacked[8];    // Array of 8 logic elements
  int         counter;        // 32-bit signed integer
  bit [3:0]   nibble;         // 4-bit, 2-state
  
  initial begin
    packed_array = 8'hFF;     // Can assign as one value
    unpacked[0] = 1'b1;       // Must assign individually
    counter = -10;            // Supports negative
    nibble = 4'b1010;         // 2-state, no X or Z
  end
endmodule

// Example 2: typedef and struct
typedef logic [7:0] byte_t;

typedef struct packed {
  logic       valid;
  logic [3:0] addr;
  logic [7:0] data;
} packet_t;

module packet_handler (
  input  packet_t pkt_in,
  output byte_t   data_out
);
  always_comb begin
    data_out = pkt_in.valid ? pkt_in.data : 8'h00;
  end
endmodule`,
      explanation: `**Packed vs Unpacked:** Packed arrays [7:0] are stored as a single vector of bits - you can slice them like my_packed[3:0]. Unpacked arrays [8] are separate storage locations.

**typedef:** Creates reusable type names. 'byte_t' is now an alias for 'logic [7:0]', making code clearer and easier to maintain.

**struct:** Groups related signals into a single type. The 'packed' keyword means it's stored as continuous bits and can be assigned as a whole.`
    },
    "systemverilog-03-always-blocks": {
      id: "SV-03",
      title: "SystemVerilog 03 – always_comb, always_ff, always_latch",
      description: "Learn intent-specific always blocks",
      difficulty: "Intermediate",
      topics: ["always_comb", "always_ff", "always_latch", "Blocking vs Non-blocking"],
      concept: `SystemVerilog introduces three specialized always blocks that declare your design intent: always_comb for combinational logic, always_ff for sequential logic, and always_latch for latches. These catch common mistakes and make code self-documenting.`,
      keyIdeas: [
        "**always_comb** - For combinational logic, automatically sensitive to all RHS signals.",
        "**always_ff** - For sequential logic with flip-flops, requires explicit clock edge.",
        "**always_latch** - For latches (usually avoided), makes intent explicit.",
        "**Automatic sensitivity** - always_comb updates on any input change.",
        "**Error checking** - Tools verify you use correct assignment operators.",
        "**Blocking (=)** in always_comb, **Non-blocking (<=)** in always_ff."
      ],
      exampleCode: `// Example 1: always_comb for combinational logic
module mux_4to1 (
  input  logic [1:0] sel,
  input  logic [7:0] a, b, c, d,
  output logic [7:0] y
);
  always_comb begin
    case (sel)
      2'b00: y = a;
      2'b01: y = b;
      2'b10: y = c;
      2'b11: y = d;
    endcase
  end
endmodule

// Example 2: always_ff for sequential logic
module shift_register (
  input  logic       clk,
  input  logic       reset,
  input  logic       data_in,
  output logic [3:0] q
);
  always_ff @(posedge clk or posedge reset) begin
    if (reset)
      q <= 4'b0;
    else
      q <= {q[2:0], data_in};  // Shift left
  end
endmodule`,
      explanation: `**always_comb:** Automatically sensitive to sel, a, b, c, d. No need to write @(*) or sensitivity lists. Use blocking assignments (=) for combinational logic.

**always_ff:** Clearly indicates flip-flops. Must specify clock edge (@(posedge clk)). Use non-blocking assignments (<=) to avoid race conditions. The shift register shifts left by concatenating the lower 3 bits with the new input.

**Error Prevention:** If you accidentally use = in always_ff or <= in always_comb, the compiler will warn you.`
    },
    "systemverilog-04-interfaces": {
      id: "SV-04",
      title: "SystemVerilog 04 – Interfaces & Modports (Intro)",
      description: "Simplify module connections with interfaces",
      difficulty: "Intermediate",
      topics: ["Interface Declaration", "Modports", "Module Connection", "Reusability"],
      concept: `Interfaces bundle related signals into a single object, reducing port lists and making designs more maintainable. Modports define direction and access control for different modules using the same interface.`,
      keyIdeas: [
        "**Interface** groups related signals into one reusable bundle.",
        "**Modport** specifies signal directions from different perspectives.",
        "**Cleaner connections** - one interface port instead of many signals.",
        "**Reusability** - define once, use everywhere.",
        "**Master/Slave pattern** - modports define which side drives which signal.",
        "**Less error-prone** - fewer individual signals to connect."
      ],
      exampleCode: `// Example 1: Simple interface
interface simple_bus;
  logic       valid;
  logic [7:0] data;
  logic       ready;
endinterface

// Example 2: Interface with modports
interface axi_lite_if;
  logic [31:0] addr;
  logic [31:0] wdata;
  logic [31:0] rdata;
  logic        write;
  logic        valid;
  logic        ready;
  
  modport master (
    output addr, wdata, write, valid,
    input  rdata, ready
  );
  
  modport slave (
    input  addr, wdata, write, valid,
    output rdata, ready
  );
endinterface

// Master module
module axi_master (
  axi_lite_if.master bus
);
  always_comb begin
    bus.addr = 32'h1000;
    bus.write = 1'b1;
    bus.valid = 1'b1;
  end
endmodule

// Slave module
module axi_slave (
  axi_lite_if.slave bus
);
  always_comb begin
    bus.rdata = 32'hDEADBEEF;
    bus.ready = bus.valid;
  end
endmodule`,
      explanation: `**Interface Declaration:** Bundles all related signals (addr, data, control) into one reusable type. Instead of declaring 6 separate ports, you declare one interface port.

**Modports:** Define signal directions from different viewpoints. The master outputs addr/wdata/write/valid and inputs rdata/ready. The slave has opposite directions. This prevents accidental wrong connections.

**Usage:** Connect modules with 'axi_lite_if.master' or 'axi_lite_if.slave' - the modport ensures correct signal directions automatically.`
    },
    "systemverilog-05-assertions": {
      id: "SV-05",
      title: "SystemVerilog 05 – Intro to SystemVerilog Assertions (SVA)",
      description: "Introduction to property-based verification",
      difficulty: "Intermediate",
      topics: ["Immediate Assertions", "Concurrent Assertions", "assert property", "Temporal Logic"],
      concept: `SystemVerilog Assertions (SVA) allow you to specify and automatically check design properties. Unlike traditional testbenches that check outputs, assertions verify temporal relationships and protocol compliance continuously.`,
      keyIdeas: [
        "**Immediate assertions** check conditions like regular if statements (combinational).",
        "**Concurrent assertions** check temporal behavior over clock cycles.",
        "**assert** checks if a property is true, fails if false.",
        "**Implication (|->)** - if antecedent is true, consequent must follow.",
        "**Temporal operators**: ##1 (next cycle), ##[1:3] (within 1-3 cycles).",
        "**Always monitoring** - assertions check continuously during simulation."
      ],
      exampleCode: `// Example 1: Immediate assertion
module immediate_assert_example (
  input logic [3:0] data
);
  always_comb begin
    assert (data < 4'd10) 
      else $error("Data exceeds maximum value!");
  end
endmodule

// Example 2: Concurrent assertions
module fifo_assertions (
  input logic clk,
  input logic write,
  input logic read,
  input logic full,
  input logic empty
);
  // Property: Write when full should not happen
  property no_write_when_full;
    @(posedge clk) full |-> !write;
  endproperty
  
  assert property (no_write_when_full)
    else $error("Attempted write to full FIFO!");
  
  // Property: After write, not empty next cycle
  property write_fills;
    @(posedge clk) (write && !full) |=> !empty;
  endproperty
  
  assert property (write_fills)
    else $error("FIFO empty after write!");
endmodule`,
      explanation: `**Immediate Assertion:** Checks the condition combinationally, like an if statement. If data >= 10, simulation prints an error. Good for simple checks.

**Concurrent Assertion - no_write_when_full:** The property says "at every clock edge, if full is true, then write must be false". The |-> is implication operator.

**Concurrent Assertion - write_fills:** Uses |=> for "next cycle implication". Says "if we write and FIFO is not full, then next cycle the FIFO must not be empty". This checks protocol correctness.

**Benefit:** Assertions monitor your design continuously. You don't need to write explicit checks in your testbench - the assertions catch violations automatically.`
    },
    // UVM Track Modules
    "uvm-01-why-uvm": {
      id: "UVM-01",
      title: "UVM 01 – Why UVM?",
      description: "Understand the motivation behind UVM",
      difficulty: "Advanced",
      topics: ["Verification Crisis", "Reusability", "Standardization", "Methodology"],
      concept: `As designs grow complex, verification becomes the bottleneck. UVM (Universal Verification Methodology) provides a standardized, reusable framework for building powerful testbenches. It solves code reuse, scalability, and collaboration challenges.`,
      keyIdeas: [
        "**Verification Crisis** - Modern chips have billions of transistors, testing all states is impossible.",
        "**Reusability** - Write once, use across multiple projects and teams.",
        "**Standardization** - Industry-standard methodology, everyone speaks the same language.",
        "**Constrained-Random Testing** - Generates millions of test cases automatically.",
        "**Coverage-Driven** - Measures what's tested, focuses on untested areas.",
        "**Built on SystemVerilog** - Uses classes, inheritance, polymorphism for flexible testbenches."
      ],
      exampleCode: `// Traditional approach (limited reusability)
module simple_test;
  reg clk, reset;
  reg [7:0] data_in;
  wire [7:0] data_out;
  
  dut my_dut(clk, reset, data_in, data_out);
  
  initial begin
    // Hardcoded test
    reset = 1; #10 reset = 0;
    data_in = 8'h12; #10;
    data_in = 8'h34; #10;
    $finish;
  end
endmodule

// UVM approach (simplified concept)
class transaction;
  rand bit [7:0] data;
  constraint valid_range { data inside {[0:100]}; }
endclass

class my_test extends uvm_test;
  transaction tr;
  
  task run_phase(uvm_phase phase);
    repeat(1000) begin
      tr = transaction::new();
      assert(tr.randomize());
      // Send to driver...
    end
  endtask
endclass`,
      explanation: `**Traditional Approach:** Hardcoded stimulus is tedious, not reusable, and only tests a few cases. If you need to test 1000 cases, you write 1000 lines.

**UVM Approach:** Define data constraints once. The randomize() function generates 1000 unique valid test cases automatically. The transaction class is reusable across projects.

**Key Benefit:** UVM separates test intent (WHAT to test) from implementation (HOW to test). You can reuse drivers, monitors, and sequences across different chips that use the same protocol.`
    },
    "uvm-02-architecture": {
      id: "UVM-02",
      title: "UVM 02 – UVM Testbench Architecture",
      description: "Learn the layered structure of a UVM testbench",
      difficulty: "Advanced",
      topics: ["Test", "Environment", "Agent", "Component Hierarchy"],
      concept: `A UVM testbench is organized in layers: Test defines what to test, Environment contains agents, Agent bundles driver/monitor/sequencer. This hierarchy enables reusability and clear separation of concerns.`,
      keyIdeas: [
        "**Test** - Top-level component, defines test scenario and configuration.",
        "**Environment** - Contains all verification components (agents, scoreboards).",
        "**Agent** - Groups driver, monitor, sequencer for one interface.",
        "**Driver** - Converts transactions to pin wiggles on DUT.",
        "**Monitor** - Observes DUT pins and reconstructs transactions.",
        "**Sequencer** - Manages transaction flow to driver.",
        "**Scoreboard** - Checks DUT behavior against expected results."
      ],
      exampleCode: `// Simplified UVM hierarchy structure
class my_test extends uvm_test;
  my_env env;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = my_env::type_id::create("env", this);
  endfunction
endclass

class my_env extends uvm_env;
  my_agent agent;
  my_scoreboard sb;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = my_agent::type_id::create("agent", this);
    sb = my_scoreboard::type_id::create("sb", this);
  endfunction
endclass

class my_agent extends uvm_agent;
  my_driver    driver;
  my_monitor   monitor;
  my_sequencer sequencer;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    driver = my_driver::type_id::create("driver", this);
    monitor = my_monitor::type_id::create("monitor", this);
    sequencer = my_sequencer::type_id::create("sequencer", this);
  endfunction
  
  function void connect_phase(uvm_phase phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction
endclass`,
      explanation: `**Hierarchy:** Test creates Environment, Environment creates Agent(s) and Scoreboard, Agent creates Driver, Monitor, and Sequencer.

**build_phase:** Each component constructs its children using type_id::create(). This is UVM's factory pattern - enables configuration and override.

**connect_phase:** After all components are built, connect them. The driver's seq_item_port connects to the sequencer to get transactions.

**Reusability:** Want to test a different chip with the same interface? Keep the Agent, just write a new Test and Environment.`
    },
    "uvm-03-transactions-sequences": {
      id: "UVM-03",
      title: "UVM 03 – Transactions, Sequences, Drivers",
      description: "Master the stimulus generation flow",
      difficulty: "Advanced",
      topics: ["Sequence Item", "Sequence", "Sequencer", "Driver"],
      concept: `The stimulus path flows: Sequence generates sequence_items (transactions), Sequencer manages the flow, Driver receives items and converts them to pin-level activity on the DUT.`,
      keyIdeas: [
        "**Sequence Item** - Data packet representing one transaction (address, data, control).",
        "**Sequence** - Generates a series of sequence items with constraints/randomization.",
        "**Sequencer** - Traffic controller, sends items from sequence to driver.",
        "**Driver** - Converts abstract transactions to actual signal toggles.",
        "**Randomization** - Constraints ensure valid but varied stimulus.",
        "**Separation** - Sequence says WHAT to send, Driver says HOW to send."
      ],
      exampleCode: `// Sequence Item (Transaction)
class my_transaction extends uvm_sequence_item;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  rand bit       write;
  
  constraint addr_range { addr < 8'h80; }
  
  \`uvm_object_utils(my_transaction)
endclass

// Sequence (generates transactions)
class my_sequence extends uvm_sequence#(my_transaction);
  \`uvm_object_utils(my_sequence)
  
  task body();
    my_transaction tr;
    repeat(10) begin
      tr = my_transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize());
      finish_item(tr);
    end
  endtask
endclass

// Driver (converts to pin wiggles)
class my_driver extends uvm_driver#(my_transaction);
  virtual dut_if vif;
  
  task run_phase(uvm_phase phase);
    my_transaction tr;
    forever begin
      seq_item_port.get_next_item(tr);
      // Drive signals
      vif.addr <= tr.addr;
      vif.data <= tr.data;
      vif.write <= tr.write;
      @(posedge vif.clk);
      seq_item_port.item_done();
    end
  endtask
endclass`,
      explanation: `**Sequence Item:** Defines what data is in a transaction. The rand keyword makes fields randomizable. Constraints guide randomization (addr must be < 128).

**Sequence:** The body() task generates 10 randomized transactions. start_item()/finish_item() handles the handshake with the driver through the sequencer.

**Driver:** Runs forever, getting transactions from the sequencer. For each transaction, it applies the abstract values (addr, data, write) to the actual DUT interface pins, then waits for a clock edge.

**Flow:** Sequence creates item → Sequencer queues it → Driver gets it → Driver wiggles pins.`
    },
    "uvm-04-monitors-scoreboards": {
      id: "UVM-04",
      title: "UVM 04 – Monitors, Scoreboards, Analysis Ports",
      description: "Learn to observe and verify DUT behavior",
      difficulty: "Advanced",
      topics: ["Monitor", "Scoreboard", "Analysis Port", "TLM"],
      concept: `While the driver sends stimulus, the monitor passively observes DUT outputs and reconstructs transactions. The scoreboard compares observed transactions against expected behavior to verify correctness.`,
      keyIdeas: [
        "**Monitor** - Passive observer, watches DUT pins and creates transactions.",
        "**Analysis Port** - TLM communication channel, broadcasts transactions.",
        "**Scoreboard** - Receives transactions, compares actual vs expected.",
        "**Passive observation** - Monitor doesn't drive signals, only watches.",
        "**TLM (Transaction-Level Modeling)** - High-level communication between components.",
        "**Automatic checking** - Scoreboard detects mismatches automatically."
      ],
      exampleCode: `// Monitor (observes DUT)
class my_monitor extends uvm_monitor;
  virtual dut_if vif;
  uvm_analysis_port#(my_transaction) ap;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
  endfunction
  
  task run_phase(uvm_phase phase);
    my_transaction tr;
    forever begin
      @(posedge vif.clk);
      if (vif.valid) begin
        tr = my_transaction::type_id::create("tr");
        tr.addr = vif.addr;
        tr.data = vif.data_out;
        ap.write(tr);  // Broadcast to scoreboard
      end
    end
  endtask
endclass

// Scoreboard (checks correctness)
class my_scoreboard extends uvm_scoreboard;
  uvm_analysis_imp#(my_transaction, my_scoreboard) ap_imp;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap_imp = new("ap_imp", this);
  endfunction
  
  function void write(my_transaction tr);
    bit [7:0] expected_data;
    
    // Compute expected value
    expected_data = compute_expected(tr.addr);
    
    // Compare
    if (tr.data != expected_data) begin
      \`uvm_error("SCOREBOARD", 
        $sformatf("Mismatch! Addr=%h Expected=%h Got=%h",
                  tr.addr, expected_data, tr.data))
    end else begin
      \`uvm_info("SCOREBOARD", "PASS", UVM_LOW)
    end
  endfunction
endclass`,
      explanation: `**Monitor:** Watches DUT output pins every clock cycle. When valid signal is high, it captures addr and data_out, packages them into a transaction, and broadcasts via analysis port (ap.write()).

**Analysis Port:** TLM communication channel. The monitor writes transactions to it, and any component can subscribe to receive them. Non-blocking, one-to-many broadcast.

**Scoreboard:** Receives transactions through ap_imp (analysis import). For each transaction, it computes what the data SHOULD be (using a reference model or golden output), then compares. Mismatches are flagged as errors.

**Automatic Verification:** As simulation runs, scoreboard continuously checks every output. No manual checking needed - errors are reported automatically.`
    },
    "uvm-05-mini-example": {
      id: "UVM-05",
      title: "UVM 05 – Putting It All Together (Mini UVM Environment)",
      description: "See all components working together",
      difficulty: "Advanced",
      topics: ["Full Example", "Component Connection", "Test Execution", "Best Practices"],
      concept: `A complete UVM testbench connects all components: Test starts sequences, Driver sends transactions to DUT, Monitor observes outputs, Scoreboard verifies correctness. All layers work together in a coordinated flow.`,
      keyIdeas: [
        "**Complete flow**: Test → Sequence → Driver → DUT → Monitor → Scoreboard.",
        "**Build phase**: Create component hierarchy top-down.",
        "**Connect phase**: Wire up TLM ports between components.",
        "**Run phase**: Sequences generate stimulus, monitors observe.",
        "**Report phase**: Print final pass/fail status.",
        "**Phases execute automatically** - UVM controls the flow."
      ],
      exampleCode: `// Complete mini UVM environment
class mini_test extends uvm_test;
  mini_env env;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = mini_env::type_id::create("env", this);
  endfunction
  
  task run_phase(uvm_phase phase);
    mini_sequence seq;
    phase.raise_objection(this);
    
    seq = mini_sequence::type_id::create("seq");
    seq.start(env.agent.sequencer);
    
    phase.drop_objection(this);
  endtask
endclass

class mini_env extends uvm_env;
  mini_agent agent;
  mini_scoreboard sb;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = mini_agent::type_id::create("agent", this);
    sb = mini_scoreboard::type_id::create("sb", this);
  endfunction
  
  function void connect_phase(uvm_phase phase);
    agent.monitor.ap.connect(sb.ap_imp);
  endfunction
endclass

// Entry point
module top;
  initial begin
    run_test("mini_test");
  end
endmodule`,
      explanation: `**Complete Flow:**
1. **top module** calls run_test("mini_test") - UVM's entry point.
2. **Build phase** runs top-down: Test creates Env, Env creates Agent and Scoreboard, Agent creates Driver/Monitor/Sequencer.
3. **Connect phase**: Monitor's analysis port connects to Scoreboard's analysis import. Now monitor can send transactions to scoreboard.
4. **Run phase**: Test creates and starts sequence on the sequencer. Sequence generates transactions → Sequencer → Driver → DUT → Monitor → Scoreboard.
5. **Objections**: raise_objection() tells UVM "I'm still working, don't end simulation". drop_objection() says "I'm done".
6. **Report phase**: UVM prints summary of errors/warnings.

**Key Insight:** You write the components (sequence, driver, monitor, scoreboard) once. UVM orchestrates the phases and connections automatically. This is the power of the methodology.`
    }
  };

  const module = modulesData[slug || "verilog-01-basics-syntax"];

  if (!module) {
    return (
      <div className="min-h-screen py-20 px-4">
        <div className="container mx-auto text-center">
          <h1 className="text-3xl font-bold mb-4">Module Not Found</h1>
          <Button onClick={() => navigate("/verilog-modules")}>
            <ArrowLeft className="mr-2" /> Back to Verilog Modules
          </Button>
        </div>
      </div>
    );
  }

  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4 max-w-4xl">
        {/* Header */}
        <Button
          variant="ghost"
          onClick={() => navigate("/verilog-modules")}
          className="mb-6"
        >
          <ArrowLeft className="mr-2" /> Back to Verilog Modules
        </Button>

        <div className="mb-8">
          <div className="flex items-center gap-3 mb-4">
            <div className="w-12 h-12 rounded-lg bg-primary/10 flex items-center justify-center">
              <Code className="w-6 h-6 text-primary" />
            </div>
            <Badge variant="outline" className="bg-green-500/10 text-green-600 border-green-500/20">
              {module.difficulty}
            </Badge>
          </div>
          <div className="text-sm text-muted-foreground font-mono mb-2">Module {module.id}</div>
          <h1 className="text-4xl font-bold mb-4">{module.title}</h1>
          <p className="text-lg text-muted-foreground mb-6">{module.description}</p>
          <div className="flex flex-wrap gap-2">
            {module.topics.map((topic: string, index: number) => (
              <Badge key={index} variant="secondary">
                {topic}
              </Badge>
            ))}
          </div>
        </div>

        <Separator className="my-8" />

        {/* Concept Summary */}
        <Card className="mb-6">
          <CardHeader>
            <CardTitle className="text-2xl">1. Introduction</CardTitle>
          </CardHeader>
          <CardContent>
            <p className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.Introduction}
            </p>
          </CardContent>
        </Card>

        {/* Key Ideas */}
       {/* <Card className="mb-6">
          <CardHeader>
            <CardTitle className="text-2xl">Module Structure</CardTitle>
          </CardHeader>
          <CardContent>
            <ul className="space-y-3">
              {module.keyIdeas.map((idea: string, index: number) => (
                <li key={index} className="flex gap-3">
                  <span className="text-primary mt-1">•</span>
                  <span className="text-muted-foreground" dangerouslySetInnerHTML={{ __html: idea }} />
                </li>
              ))}
            </ul>
          </CardContent>
        </Card> */}
        
        <Card className="mb-6">
          <CardHeader>
            <CardTitle className="text-2xl">2.Verilog Module Structure</CardTitle>
          </CardHeader>
          <CardContent>
            <p className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.ModuleStructure}
            </p>
          </CardContent>
          <CardHeader>
            <CardTitle className="text-2xl">Syntax</CardTitle>
            </CardHeader>
          <CardContent>
            <p className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.Syntax}
            </p>
          </CardContent>

        {/* Example Code */}
       {/*} <Card className="mb-6">*/}
          <CardHeader>
            <CardTitle className="text-2xl">Example: AND Gate</CardTitle>
          </CardHeader>
          <CardContent>
            <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
              <code className="text-sm font-mono">{module.Example}</code>
            </pre>
          </CardContent>
        </Card>

        {/* Data types */}
        <Card className="mb-8">
          <CardHeader>
            <CardTitle className="text-2xl">3. Data Types in Verilog</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.datatypes}
            </div>
          </CardContent>
           <CardHeader>
            <CardTitle className="text-2xl">Vectors</CardTitle>
            </CardHeader>
          <CardContent>
            <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
              <code className="text-sm font-mono">{module.vectors}</code>
            </pre>
          </CardContent>
        </Card>
      {/* Operators */}
       <Card className="mb-8">
          <CardHeader>
            <CardTitle className="text-2xl">4. Operators</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.operator}
            </div>
          </CardContent>
           <CardHeader>
            <CardTitle className="text-2xl">Example Operator Use</CardTitle>
            </CardHeader>
          <CardContent>
            <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
              <code className="text-sm font-mono">{module.exampleOperator}</code>
            </pre>
          </CardContent>
        </Card>
        {/* Continuous Assignment */}
        <Card className="mb-8">
          <CardHeader>
            <CardTitle className="text-2xl">5. Continuous Assignment</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.continuousAssignment}
            </div>
          </CardContent>
        </Card>
        {/* Operators */}
       <Card className="mb-8">
          <CardHeader>
            <CardTitle className="text-2xl">6. Procedural Blocks in Verilog</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.proceduralBlocks}
            </div>
          </CardContent>
           <CardHeader>
            <CardTitle className="text-2xl">6.1 Combinational Logic (`always @(*)`)</CardTitle>
            </CardHeader>
          <CardContent>
            <p className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.combinationalLogic}
            </p>
          </CardContent>
          <CardHeader>
            <CardTitle className="text-2xl">6.2 Sequential Logic (`always @(posedge clk)`)</CardTitle>
            </CardHeader>
          <CardContent>
            <p className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.sequentialLogic}
            </p>
          </CardContent>
        </Card>
          {/* Control Statements */}
       <Card className="mb-8">
          <CardHeader>
            <CardTitle className="text-2xl">7. Control Statements</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.controlStatements}
            </div>
          </CardContent>
           <CardHeader>
            <CardTitle className="text-2xl">If–Else Example</CardTitle>
            </CardHeader>
          <CardContent>
             <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
              <code className="text-sm font-mono">{module.ifElseExample}</code>
            </pre>
          </CardContent>
          <CardHeader>
            <CardTitle className="text-2xl">Case Example</CardTitle>
            </CardHeader>
          <CardContent>
             <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
              <code className="text-sm font-mono">{module.caseExample}</code>
            </pre>
          </CardContent>
        </Card>
        {/* Example Circuits */}
       <Card className="mb-8">
          <CardHeader>
            <CardTitle className="text-2xl">8. Example Circuits</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.exampleCircuits}
            </div>
          </CardContent>
           <CardHeader>
            <CardTitle className="text-2xl">2:1 Multiplexer</CardTitle>
            </CardHeader>
          <CardContent>
            <p className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.multiplexer}
            </p>
          </CardContent>
          <CardHeader>
            <CardTitle className="text-2xl">D Flip-Flop</CardTitle>
            </CardHeader>
          <CardContent>
            <p className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.DflipFlop}
            </p>
          </CardContent>
        </Card>
        {/* Common Beginner Mistakes */}
        <Card className="mb-8">
          <CardHeader>
            <CardTitle className="text-2xl">9. Common Beginner Mistakes</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.commonBeginnerMistakes}
            </div>
          </CardContent>
        </Card>
        {/* Navigation */}
        <div className="flex justify-between">
          <Button 
            variant="outline"
            onClick={() => navigate("/verilog-modules")}
          >
            <ArrowLeft className="mr-2" /> All Modules
          </Button>
        </div>
      </div>
    </div>
  );
};

export default ModuleDetail;
