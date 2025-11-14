import { useParams, useNavigate } from "react-router-dom";
import { Button } from "@/components/ui/button";
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { Separator } from "@/components/ui/separator";
import { ArrowLeft, ExternalLink, Code, FileText, HelpCircle } from "lucide-react";

const ModuleDetail = () => {
  const { id } = useParams();
  const navigate = useNavigate();

  // Module data (matches the structure in Modules.tsx)
  const modulesData: Record<string, any> = {
    "01": {
      id: "01",
      title: "Verilog Basics",
      description: "Introduction to hardware description, modules, and basic syntax",
      difficulty: "Beginner",
      topics: ["Data Types", "Operators", "Module Structure"],
      concept: "Verilog is a Hardware Description Language (HDL) used to model electronic systems. It allows you to describe the behavior and structure of digital circuits at various levels of abstraction. In this module, you'll learn the fundamental building blocks: data types (wire, reg), operators (logical, arithmetic), and how to structure a basic module with inputs and outputs.",
      exampleCode: `// Simple 2-to-1 Multiplexer
module mux2to1 (
  input wire a,
  input wire b,
  input wire sel,
  output wire y
);

  assign y = sel ? b : a;

endmodule

// Testbench
module tb_mux2to1;
  reg a, b, sel;
  wire y;

  mux2to1 dut (.a(a), .b(b), .sel(sel), .y(y));

  initial begin
    $monitor("Time=%0t | a=%b b=%b sel=%b | y=%b", 
             $time, a, b, sel, y);
    
    a = 0; b = 1; sel = 0; #10;
    sel = 1; #10;
    a = 1; b = 0; sel = 0; #10;
    sel = 1; #10;
    
    $finish;
  end
endmodule`,
      expectedOutput: "When sel=0, output y follows input a. When sel=1, output y follows input b. The waveform will show the multiplexer selecting between two inputs based on the select signal.",
      quiz: [
        { question: "What is the difference between 'wire' and 'reg' in Verilog?", answer: "Wire represents continuous assignment, while reg holds values until reassigned." },
        { question: "What does the 'assign' statement do?", answer: "It creates continuous assignment for combinational logic." }
      ]
    },
    "02": {
      id: "02",
      title: "Counters and FSMs",
      description: "Build counters and finite state machines with practical examples",
      difficulty: "Beginner",
      topics: ["Sequential Logic", "State Machines", "Timing"],
      concept: "Sequential logic circuits have memory elements and change states based on clock signals. Counters increment/decrement values, while Finite State Machines (FSMs) transition between defined states based on inputs. Understanding timing, setup, and hold constraints is crucial for reliable sequential designs.",
      exampleCode: `// 4-bit Up Counter with Reset
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

endmodule

// Simple FSM - Traffic Light Controller
module traffic_light (
  input wire clk,
  input wire reset,
  output reg [1:0] light
);

  localparam GREEN  = 2'b00;
  localparam YELLOW = 2'b01;
  localparam RED    = 2'b10;
  
  reg [1:0] state, next_state;
  reg [3:0] timer;

  always @(posedge clk or posedge reset) begin
    if (reset) state <= GREEN;
    else state <= next_state;
  end

  always @(*) begin
    case (state)
      GREEN:  next_state = (timer == 9) ? YELLOW : GREEN;
      YELLOW: next_state = (timer == 2) ? RED : YELLOW;
      RED:    next_state = (timer == 9) ? GREEN : RED;
      default: next_state = GREEN;
    endcase
  end

  assign light = state;

endmodule`,
      expectedOutput: "The counter increments from 0000 to 1111 on each clock cycle, then wraps around. The FSM cycles through GREEN (9 cycles) → YELLOW (2 cycles) → RED (9 cycles) states continuously.",
      quiz: [
        { question: "What triggers a state change in sequential logic?", answer: "A clock edge (posedge or negedge)." },
        { question: "Why do we need separate always blocks for state and next_state?", answer: "To separate sequential (state update) from combinational (next state logic) behavior." }
      ]
    },
    "03": {
      id: "03",
      title: "Combinational Circuits",
      description: "Design adders, multiplexers, and other combinational logic",
      difficulty: "Intermediate",
      topics: ["Adders", "Multiplexers", "Decoders"],
      concept: "Combinational circuits produce outputs solely based on current inputs with no memory. Key building blocks include adders (arithmetic operations), multiplexers (data selection), and decoders (address decoding). These circuits form the foundation of data paths in processors and digital systems.",
      exampleCode: `// 4-bit Ripple Carry Adder
module full_adder (
  input wire a, b, cin,
  output wire sum, cout
);

  assign sum = a ^ b ^ cin;
  assign cout = (a & b) | (b & cin) | (cin & a);

endmodule

module ripple_carry_adder_4bit (
  input wire [3:0] a, b,
  input wire cin,
  output wire [3:0] sum,
  output wire cout
);

  wire c1, c2, c3;

  full_adder fa0 (.a(a[0]), .b(b[0]), .cin(cin), .sum(sum[0]), .cout(c1));
  full_adder fa1 (.a(a[1]), .b(b[1]), .cin(c1), .sum(sum[1]), .cout(c2));
  full_adder fa2 (.a(a[2]), .b(b[2]), .cin(c2), .sum(sum[2]), .cout(c3));
  full_adder fa3 (.a(a[3]), .b(b[3]), .cin(c3), .sum(sum[3]), .cout(cout));

endmodule

// 4-to-1 Multiplexer
module mux4to1 (
  input wire [3:0] data,
  input wire [1:0] sel,
  output wire out
);

  assign out = data[sel];

endmodule`,
      expectedOutput: "The 4-bit adder adds two 4-bit numbers with carry propagation. For example: 0101 + 0011 = 1000. The multiplexer selects one of four inputs based on the 2-bit select signal.",
      quiz: [
        { question: "What causes delay in a ripple carry adder?", answer: "Carry propagation through each full adder stage sequentially." },
        { question: "How does a multiplexer use the select signal?", answer: "It uses the select bits as an index to choose which input to route to the output." }
      ]
    },
    "04": {
      id: "04",
      title: "SystemVerilog Fundamentals",
      description: "Explore enhanced features of SystemVerilog for verification",
      difficulty: "Intermediate",
      topics: ["Classes", "Interfaces", "Assertions"],
      concept: "SystemVerilog extends Verilog with object-oriented programming features, enhanced data types, and powerful verification constructs. Classes enable reusable test components, interfaces simplify port connections, and assertions verify design properties during simulation.",
      exampleCode: `// SystemVerilog Class Example
class Transaction;
  rand bit [7:0] addr;
  rand bit [31:0] data;
  rand bit write;
  
  constraint addr_range { addr inside {[0:127]}; }
  
  function void display();
    $display("Addr: %0h, Data: %0h, Write: %0b", addr, data, write);
  endfunction
endclass

// Interface Example
interface bus_if (input logic clk);
  logic [7:0] addr;
  logic [31:0] data;
  logic valid;
  logic ready;
  
  clocking cb @(posedge clk);
    output addr, data, valid;
    input ready;
  endclocking
  
  modport master (clocking cb);
  modport slave (input addr, data, valid, output ready);
endinterface

// Assertion Example
module fifo_checker (
  input logic clk, reset,
  input logic push, pop,
  input logic full, empty
);

  // Property: FIFO cannot be full and empty simultaneously
  property no_full_empty;
    @(posedge clk) disable iff (reset)
    !(full && empty);
  endproperty
  
  assert property (no_full_empty)
    else $error("FIFO is both full and empty!");

endmodule`,
      expectedOutput: "Classes create randomized transactions, interfaces bundle signals cleanly, and assertions catch protocol violations like a FIFO being full and empty at the same time.",
      quiz: [
        { question: "What is the advantage of using interfaces?", answer: "Interfaces bundle related signals and simplify port connections between modules." },
        { question: "What do assertions verify?", answer: "Assertions verify that design properties and protocols are followed during simulation." }
      ]
    },
    "05": {
      id: "05",
      title: "UVM Basics",
      description: "Introduction to Universal Verification Methodology",
      difficulty: "Advanced",
      topics: ["Testbenches", "Sequences", "Scoreboards"],
      concept: "UVM (Universal Verification Methodology) is an industry-standard framework for building reusable, scalable testbenches. It provides base classes for components like drivers, monitors, agents, and scoreboards. UVM promotes a structured approach with phases for build, connect, run, and check.",
      exampleCode: `// UVM Sequence Item
class my_transaction extends uvm_sequence_item;
  rand bit [7:0] addr;
  rand bit [31:0] data;
  rand bit wr_rd;
  
  \`uvm_object_utils_begin(my_transaction)
    \`uvm_field_int(addr, UVM_ALL_ON)
    \`uvm_field_int(data, UVM_ALL_ON)
    \`uvm_field_int(wr_rd, UVM_ALL_ON)
  \`uvm_object_utils_end
  
  function new(string name = "my_transaction");
    super.new(name);
  endfunction
endclass

// UVM Driver
class my_driver extends uvm_driver #(my_transaction);
  \`uvm_component_utils(my_driver)
  
  virtual bus_if vif;
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);
      drive_transaction(req);
      seq_item_port.item_done();
    end
  endtask
  
  task drive_transaction(my_transaction trans);
    @(posedge vif.clk);
    vif.addr <= trans.addr;
    vif.data <= trans.data;
    vif.wr_rd <= trans.wr_rd;
  endtask
endclass

// UVM Sequence
class my_sequence extends uvm_sequence #(my_transaction);
  \`uvm_object_utils(my_sequence)
  
  function new(string name = "my_sequence");
    super.new(name);
  endfunction
  
  task body();
    repeat(10) begin
      req = my_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize());
      finish_item(req);
    end
  endtask
endclass`,
      expectedOutput: "UVM creates structured testbenches where sequences generate transactions, drivers send them to the DUT, and monitors observe responses. The framework manages phases and provides reporting.",
      quiz: [
        { question: "What is the role of a UVM driver?", answer: "The driver converts transaction-level data into pin-level signals for the DUT." },
        { question: "What is a UVM sequence?", answer: "A sequence generates stimulus (transactions) that are sent to the driver." }
      ]
    },
    "06": {
      id: "06",
      title: "Advanced UVM",
      description: "Deep dive into UVM factories, configs, and advanced patterns",
      difficulty: "Advanced",
      topics: ["Factory Pattern", "Configuration", "Phasing"],
      concept: "Advanced UVM techniques include the factory pattern for overriding components, configuration databases for passing parameters, virtual sequences for coordinating multiple sequences, and advanced phasing for complex test scenarios. These enable highly flexible and reusable verification environments.",
      exampleCode: `// Factory Override Example
class base_driver extends uvm_driver #(my_transaction);
  \`uvm_component_utils(base_driver)
  
  task drive_transaction(my_transaction trans);
    // Standard implementation
    $display("Base driver executing");
  endtask
endclass

class enhanced_driver extends base_driver;
  \`uvm_component_utils(enhanced_driver)
  
  task drive_transaction(my_transaction trans);
    // Enhanced with additional checks
    $display("Enhanced driver with extra features");
    super.drive_transaction(trans);
  endtask
endclass

// In test:
// set_type_override_by_type(base_driver::get_type(), 
//                           enhanced_driver::get_type());

// Configuration Database Usage
class my_agent extends uvm_agent;
  my_driver drv;
  virtual bus_if vif;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    if (!uvm_config_db#(virtual bus_if)::get(this, "", "vif", vif))
      \`uvm_fatal("NO_VIF", "Virtual interface not found")
    
    drv = my_driver::type_id::create("drv", this);
    uvm_config_db#(virtual bus_if)::set(this, "drv", "vif", vif);
  endfunction
endclass

// Virtual Sequence for Multi-agent Coordination
class virtual_sequence extends uvm_sequence;
  \`uvm_object_utils(virtual_sequence)
  
  seq_a_type seq_a;
  seq_b_type seq_b;
  
  task body();
    fork
      begin
        seq_a = seq_a_type::type_id::create("seq_a");
        seq_a.start(p_sequencer.seqr_a);
      end
      begin
        seq_b = seq_b_type::type_id::create("seq_b");
        seq_b.start(p_sequencer.seqr_b);
      end
    join
  endtask
endclass`,
      expectedOutput: "Factory overrides allow swapping components without changing testbench structure. Config DB passes parameters hierarchically. Virtual sequences coordinate multiple agents for complex scenarios.",
      quiz: [
        { question: "What is the benefit of the UVM factory pattern?", answer: "It allows runtime component substitution without modifying the testbench structure." },
        { question: "How does uvm_config_db help in verification?", answer: "It provides a centralized database for passing configuration parameters across the hierarchy." }
      ]
    }
  };

  const module = modulesData[id || "01"];

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
            <p className="text-muted-foreground leading-relaxed">{module.concept}</p>
          </CardContent>
        </Card>

        {/* 2. Example Code */}
        <Card className="mb-8">
          <CardHeader>
            <div className="flex items-center gap-2">
              <Code className="w-5 h-5 text-primary" />
              <CardTitle>Example Code</CardTitle>
            </div>
            <CardDescription>SystemVerilog implementation</CardDescription>
          </CardHeader>
          <CardContent>
            <pre className="bg-muted p-4 rounded-lg overflow-x-auto">
              <code className="text-sm font-mono">{module.exampleCode}</code>
            </pre>
          </CardContent>
        </Card>

        {/* 3. Run Simulation Button */}
        <Card className="mb-8">
          <CardContent className="pt-6">
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
                  <ExternalLink className="mr-2" /> Run Simulation
                </a>
              </Button>
            </div>
          </CardContent>
        </Card>

        {/* 4. Expected Output */}
        <Card className="mb-8">
          <CardHeader>
            <CardTitle>Expected Output</CardTitle>
            <CardDescription>What you should see when running the simulation</CardDescription>
          </CardHeader>
          <CardContent>
            <div className="bg-muted p-4 rounded-lg mb-4">
              <p className="text-sm font-mono text-muted-foreground">{module.expectedOutput}</p>
            </div>
            <div className="aspect-video bg-muted rounded-lg flex items-center justify-center border-2 border-dashed border-border">
              <p className="text-muted-foreground text-sm">Waveform screenshot placeholder</p>
            </div>
          </CardContent>
        </Card>

        {/* 5. Reflection / Quiz Section */}
        <Card className="mb-8">
          <CardHeader>
            <div className="flex items-center gap-2">
              <HelpCircle className="w-5 h-5 text-primary" />
              <CardTitle>Reflection & Quiz</CardTitle>
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
            onClick={() => {
              const prevId = String(Number(module.id) - 1).padStart(2, '0');
              if (Number(prevId) >= 1) navigate(`/modules/${prevId}`);
            }}
            disabled={module.id === "01"}
          >
            <ArrowLeft className="mr-2" /> Previous Module
          </Button>
          <Button 
            variant="outline"
            onClick={() => {
              const nextId = String(Number(module.id) + 1).padStart(2, '0');
              if (Number(nextId) <= 6) navigate(`/modules/${nextId}`);
            }}
            disabled={module.id === "06"}
          >
            Next Module <ExternalLink className="ml-2" />
          </Button>
        </div>
      </div>
    </div>
  );
};

export default ModuleDetail;
