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
    "verilog-05-mini-project": {
      id: "VF-05",
      title: "Verilog 05 – Mini Project",
      description: "Build a complete 4-bit counter with load and reset",
      difficulty: "Beginner",
      topics: ["Counter Design", "Control Signals", "State Management", "Testing"],
      concept: `In this mini project, you'll design a 4-bit up counter with synchronous load and asynchronous reset.

**Features:**
- **4-bit counter**: Counts from 0 to 15
- **Load signal**: Loads a parallel value when asserted
- **Reset signal**: Asynchronously resets counter to 0
- **Enable signal**: Controls counting

**Design Requirements:**
1. Count up on each clock edge when enabled
2. Load parallel data when load signal is high
3. Reset to 0 when reset is asserted
4. Wrap around from 15 to 0`,
      keySyntax: `// Counter control priority:
// 1. Asynchronous reset (highest)
// 2. Synchronous load
// 3. Count enable
// 4. Hold current value (default)

always @(posedge clk or posedge reset) begin
  if (reset)
    // Reset action
  else if (load)
    // Load action
  else if (enable)
    // Count action
end`,
      exampleCode: `// 4-bit Counter with Load and Reset
module counter_4bit (
  input wire clk,
  input wire reset,
  input wire load,
  input wire enable,
  input wire [3:0] data,
  output reg [3:0] count
);
  always @(posedge clk or posedge reset) begin
    if (reset)
      count <= 4'b0000;
    else if (load)
      count <= data;
    else if (enable)
      count <= count + 1;
  end
endmodule

// Testbench
module tb_counter_4bit;
  reg clk, reset, load, enable;
  reg [3:0] data;
  wire [3:0] count;
  
  counter_4bit uut (
    .clk(clk),
    .reset(reset),
    .load(load),
    .enable(enable),
    .data(data),
    .count(count)
  );
  
  // Clock generation
  initial clk = 0;
  always #5 clk = ~clk;
  
  initial begin
    $display("Time\\tRst\\tLd\\tEn\\tData\\tCount");
    $monitor("%0t\\t%b\\t%b\\t%b\\t%h\\t%h", 
             $time, reset, load, enable, data, count);
    
    // Test reset
    reset = 1; load = 0; enable = 0; data = 0;
    #10 reset = 0;
    
    // Test counting
    #10 enable = 1;
    #80 enable = 0;
    
    // Test load
    #10 load = 1; data = 4'hA;
    #10 load = 0; enable = 1;
    #40 $finish;
  end
endmodule`,
      expectedOutput: `Time  Rst Ld  En  Data Count
0     1   0   0   0    0
10    0   0   0   0    0
20    0   0   1   0    1
30    0   0   1   0    2
40    0   0   1   0    3
...
90    0   0   1   0    8
100   0   0   0   0    8
110   0   1   0   A    A
120   0   0   1   A    B
130   0   0   1   A    C
...

The counter:
1. Resets to 0
2. Counts up when enabled (0→1→2...→8)
3. Loads value A (10) when load is asserted
4. Continues counting from A (A→B→C→D...)`,
      quiz: [
        { question: "What happens when reset is asserted?", answer: "Counter resets to 0 immediately (asynchronous)" },
        { question: "What is the priority between load and enable?", answer: "Load has higher priority than enable" },
        { question: "What value does the counter wrap to after 15 (F)?", answer: "0" },
        { question: "Is the reset synchronous or asynchronous?", answer: "Asynchronous (doesn't wait for clock)" },
        { question: "What happens when enable=0?", answer: "Counter holds its current value" }
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
