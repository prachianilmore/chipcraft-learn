import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Badge } from "@/components/ui/badge";
import { Code, ArrowLeft, ArrowRight } from "lucide-react";
import { useNavigate } from "react-router-dom";

const VerilogModules = () => {
  const navigate = useNavigate();

  const modules = [
    {
      id: "VF-01",
      slug: "verilog-01-basics-syntax",
      title: "Verilog 01 – Basics & Syntax",
      description: "Learn fundamental Verilog syntax, module structure, and basic operators",
      topics: ["Module Declaration", "Data Types", "Operators", "Basic Syntax"]
    },
    {
      id: "VF-02",
      slug: "verilog-02-combinational-logic",
      title: "Verilog 02 – Combinational Logic",
      description: "Master combinational circuits including gates, multiplexers, and decoders",
      topics: ["Logic Gates", "assign Statements", "Multiplexers", "Decoders"]
    },
    {
      id: "VF-03",
      slug: "verilog-03-sequential-logic",
      title: "Verilog 03 – Sequential Logic",
      description: "Understand sequential circuits, flip-flops, and always blocks",
      topics: ["always Blocks", "Flip-Flops", "Registers", "Clocking"]
    },
    {
      id: "VF-04",
      slug: "verilog-04-testbenches",
      title: "Verilog 04 – Verilog Testbenches",
      description: "Write testbenches to verify your Verilog designs",
      topics: ["Testbench Structure", "initial Blocks", "Stimulus", "$display"]
    }
  ];

  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4">
        {/* Back Button */}
        <Button 
          variant="ghost" 
          onClick={() => navigate("/modules")}
          className="mb-6"
        >
          <ArrowLeft className="mr-2 w-4 h-4" /> Back to Tracks
        </Button>

        {/* Header */}
        <div className="max-w-3xl mb-12">
          <div className="flex items-center gap-3 mb-4">
            <div className="w-12 h-12 rounded-lg bg-primary/10 flex items-center justify-center">
              <Code className="w-6 h-6 text-primary" />
            </div>
            <h1 className="text-4xl md:text-5xl font-bold">Verilog Fundamentals</h1>
          </div>
          <p className="text-lg text-muted-foreground">
            Master the fundamentals of Verilog HDL through 4 comprehensive modules. 
            Each module includes concept summaries, code examples, and clear explanations.
          </p>
        </div>

        {/* Modules Grid */}
        <div className="grid md:grid-cols-2 gap-6">
          {modules.map((module) => (
            <Card 
              key={module.id} 
              className="border-border hover:shadow-glow transition-all duration-300 hover:-translate-y-1 flex flex-col"
            >
              <CardHeader>
                <div className="flex items-start justify-between mb-2">
                  <div className="w-10 h-10 rounded-lg bg-primary/10 flex items-center justify-center">
                    <Code className="w-5 h-5 text-primary" />
                  </div>
                  <Badge variant="outline" className="bg-green-500/10 text-green-600 border-green-500/20">
                    Beginner
                  </Badge>
                </div>
                <div className="space-y-1">
                  <div className="text-sm text-muted-foreground font-mono">Module {module.id}</div>
                  <CardTitle className="text-xl">{module.title}</CardTitle>
                </div>
                <CardDescription>{module.description}</CardDescription>
              </CardHeader>
              <CardContent className="flex-1 flex flex-col justify-between">
                <div className="flex flex-wrap gap-2 mb-6">
                  {module.topics.map((topic, index) => (
                    <Badge key={index} variant="secondary" className="text-xs">
                      {topic}
                    </Badge>
                  ))}
                </div>
                <Button 
                  variant="default" 
                  className="w-full"
                  onClick={() => navigate(`/modules/${module.slug}`)}
                >
                  Start Module <ArrowRight className="ml-2 w-4 h-4" />
                </Button>
              </CardContent>
            </Card>
          ))}
        </div>
      </div>
    </div>
  );
};

export default VerilogModules;
