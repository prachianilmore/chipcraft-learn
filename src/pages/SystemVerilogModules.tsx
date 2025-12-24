import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Badge } from "@/components/ui/badge";
import { Code, ArrowLeft, ArrowRight } from "lucide-react";
import { useNavigate } from "react-router-dom";

const SystemVerilogModules = () => {
  const navigate = useNavigate();

  const modules = [
    {
      id: "SV-01",
      slug: "systemverilog-01-from-verilog",
      title: "SystemVerilog 01 – From Verilog to SystemVerilog",
      description: "Understand the key improvements SystemVerilog brings over traditional Verilog",
      topics: ["Introduction", "Why SystemVerilog was Introduced", "Key Improvements Over Verilog", "Enhanced Procedural Blocks","logic Data Type","Example: Sequential Logic","Common Beginner Mistakes"]
    },
    {
      id: "SV-02",
      slug: "systemverilog-02-data-types",
      title: "SystemVerilog 02 – Data Types, Arrays, typedef",
      description: "Master SystemVerilog's rich type system including packed/unpacked arrays and user-defined types",
      topics: ["Introduction", "SystemVerilog Data Types", "logic vs reg vs wire", "Packed Arrays","Unpacked Arrays","Packed and Unpacked Together","typedef","struct","union","Common Mistakes"]
    },
    {
      id: "SV-03",
      slug: "systemverilog-03-always-blocks",
      title: "SystemVerilog 03 – always_comb, always_ff, always_latch",
      description: "Learn the intent-specific always blocks that improve code clarity and catch errors",
      topics: ["always_comb", "always_ff", "always_latch", "Blocking vs Non-blocking"]
    },
    {
      id: "SV-04",
      slug: "systemverilog-04-interfaces",
      title: "SystemVerilog 04 – Interfaces & Modports (Intro)",
      description: "Simplify module connections with interfaces and control signal direction with modports",
      topics: ["Interface Declaration", "Modports", "Module Connection", "Reusability"]
    },
    {
      id: "SV-05",
      slug: "systemverilog-05-assertions",
      title: "SystemVerilog 05 – Intro to SystemVerilog Assertions (SVA)",
      description: "Introduction to property-based verification using SystemVerilog Assertions",
      topics: ["Immediate Assertions", "Concurrent Assertions", "assert property", "Temporal Logic"]
    }
  ];

  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4">
        {/* Header */}
        <Button
          variant="ghost"
          onClick={() => navigate("/modules")}
          className="mb-6"
        >
          <ArrowLeft className="mr-2" /> Back to Tracks
        </Button>

        <div className="max-w-3xl mb-12">
          <div className="flex items-center gap-3 mb-4">
            <div className="w-12 h-12 rounded-lg bg-primary/10 flex items-center justify-center">
              <Code className="w-6 h-6 text-primary" />
            </div>
            <Badge variant="outline" className="bg-blue-500/10 text-blue-600 border-blue-500/20">
              Intermediate
            </Badge>
          </div>
          <h1 className="text-4xl md:text-5xl font-bold mb-4">SystemVerilog Track</h1>
          <p className="text-lg text-muted-foreground">
            Advance from Verilog to SystemVerilog with modern features, enhanced data types, and verification capabilities.
          </p>
        </div>

        {/* Module Cards */}
        <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-6">
          {modules.map((module) => (
            <Card 
              key={module.id}
              className="border-border hover:shadow-glow transition-all duration-300 hover:-translate-y-1 cursor-pointer flex flex-col"
              onClick={() => navigate(`/modules/${module.slug}`)}
            >
              <CardHeader>
                <div className="flex items-center justify-between mb-2">
                  <div className="text-sm text-muted-foreground font-mono">{module.id}</div>
                </div>
                <CardTitle className="text-xl">{module.title}</CardTitle>
                <CardDescription>{module.description}</CardDescription>
              </CardHeader>
              <CardContent className="flex-1 flex flex-col justify-between">
                <div className="flex flex-wrap gap-2 mb-4">
                  {module.topics.map((topic, index) => (
                    <Badge key={index} variant="secondary" className="text-xs">
                      {topic}
                    </Badge>
                  ))}
                </div>
                <Button variant="ghost" className="w-full">
                  View Module <ArrowRight className="ml-2 w-4 h-4" />
                </Button>
              </CardContent>
            </Card>
          ))}
        </div>
      </div>
    </div>
  );
};

export default SystemVerilogModules;
