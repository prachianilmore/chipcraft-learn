import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Badge } from "@/components/ui/badge";
import { Code, ArrowLeft, ArrowRight } from "lucide-react";
import { useNavigate } from "react-router-dom";

const UVMModules = () => {
  const navigate = useNavigate();

  const modules = [
    {
      id: "UVM-01",
      slug: "uvm-01-why-uvm",
      title: "UVM 01 – Why UVM?",
      description: "Understand the motivation behind UVM and how it solves verification challenges",
      topics: ["Verification Crisis", "Reusability", "Standardization", "Methodology"]
    },
    {
      id: "UVM-02",
      slug: "uvm-02-architecture",
      title: "UVM 02 – UVM Testbench Architecture",
      description: "Learn the layered structure of a UVM testbench and how components work together",
      topics: ["Test", "Environment", "Agent", "Component Hierarchy"]
    },
    {
      id: "UVM-03",
      slug: "uvm-03-transactions-sequences",
      title: "UVM 03 – Transactions, Sequences, Drivers",
      description: "Master the data flow from sequence items through sequences to drivers",
      topics: ["Sequence Item", "Sequence", "Sequencer", "Driver"]
    },
    {
      id: "UVM-04",
      slug: "uvm-04-monitors-scoreboards",
      title: "UVM 04 – Monitors, Scoreboards, Analysis Ports",
      description: "Learn how to observe DUT signals and verify correct behavior automatically",
      topics: ["Monitor", "Scoreboard", "Analysis Port", "TLM"]
    },
    {
      id: "UVM-05",
      slug: "uvm-05-mini-example",
      title: "UVM 05 – Putting It All Together (Mini UVM Environment)",
      description: "See how all UVM components connect in a simple but complete testbench",
      topics: ["Full Example", "Component Connection", "Test Execution", "Best Practices"]
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
            <Badge variant="outline" className="bg-purple-500/10 text-purple-600 border-purple-500/20">
              Advanced
            </Badge>
          </div>
          <h1 className="text-4xl md:text-5xl font-bold mb-4">UVM Basics Track</h1>
          <p className="text-lg text-muted-foreground">
            Learn Universal Verification Methodology fundamentals for building scalable, reusable verification environments.
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

export default UVMModules;
