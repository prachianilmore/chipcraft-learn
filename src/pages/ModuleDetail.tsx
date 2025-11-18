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
      topics: ["Module Declaration", "Data Types", "Operators", "Basic Syntax"],
      concept: `Verilog is a Hardware Description Language (HDL) used to model digital circuits. Unlike software programming, Verilog describes hardware that operates in parallel.`,
      keyIdeas: [
        "**Modules** are the basic building blocks in Verilog. Every design starts with a module.",
        "**Ports** define interfaces to the outside world: input, output, or inout.",
        "**Data Types**: Use 'wire' for combinational logic and 'reg' for sequential logic.",
        "**Operators** are similar to C: & (AND), | (OR), ^ (XOR), ~ (NOT), +, -, *, /",
        "**assign** statements create continuous assignments for combinational logic."
      ],
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
      explanation: `**AND Gate:** The output 'y' is high only when both inputs 'a' and 'b' are high. The assign statement creates a continuous assignment.

**4-bit Adder:** Adds two 4-bit numbers. The concatenation {carry_out, sum} captures both the 4-bit sum and the carry bit. For example, adding 15 (1111) and 1 (0001) gives sum=0 (0000) and carry_out=1.`
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
            <CardTitle className="text-2xl">Concept Summary</CardTitle>
          </CardHeader>
          <CardContent>
            <p className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.concept}
            </p>
          </CardContent>
        </Card>

        {/* Key Ideas */}
        <Card className="mb-6">
          <CardHeader>
            <CardTitle className="text-2xl">Key Ideas</CardTitle>
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
        </Card>

        {/* Example Code */}
        <Card className="mb-6">
          <CardHeader>
            <CardTitle className="text-2xl">Example Code</CardTitle>
          </CardHeader>
          <CardContent>
            <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
              <code className="text-sm font-mono">{module.exampleCode}</code>
            </pre>
          </CardContent>
        </Card>

        {/* Explanation */}
        <Card className="mb-8">
          <CardHeader>
            <CardTitle className="text-2xl">Code Explanation</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="text-muted-foreground leading-relaxed whitespace-pre-line">
              {module.explanation}
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
