import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Badge } from "@/components/ui/badge";
import { Code, ExternalLink, CheckCircle } from "lucide-react";

const Modules = () => {
  const modules = [
    {
      id: "01",
      title: "Verilog Basics",
      description: "Introduction to hardware description, modules, and basic syntax",
      difficulty: "Beginner",
      topics: ["Data Types", "Operators", "Module Structure"],
      completed: false,
    },
    {
      id: "02",
      title: "Counters and FSMs",
      description: "Build counters and finite state machines with practical examples",
      difficulty: "Beginner",
      topics: ["Sequential Logic", "State Machines", "Timing"],
      completed: false,
    },
    {
      id: "03",
      title: "Combinational Circuits",
      description: "Design adders, multiplexers, and other combinational logic",
      difficulty: "Intermediate",
      topics: ["Adders", "Multiplexers", "Decoders"],
      completed: false,
    },
    {
      id: "04",
      title: "SystemVerilog Fundamentals",
      description: "Explore enhanced features of SystemVerilog for verification",
      difficulty: "Intermediate",
      topics: ["Classes", "Interfaces", "Assertions"],
      completed: false,
    },
    {
      id: "05",
      title: "UVM Basics",
      description: "Introduction to Universal Verification Methodology",
      difficulty: "Advanced",
      topics: ["Testbenches", "Sequences", "Scoreboards"],
      completed: false,
    },
    {
      id: "06",
      title: "Advanced UVM",
      description: "Deep dive into UVM factories, configs, and advanced patterns",
      difficulty: "Advanced",
      topics: ["Factory Pattern", "Configuration", "Phasing"],
      completed: false,
    },
  ];

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
      <div className="container mx-auto px-4">
        {/* Header */}
        <div className="max-w-3xl mb-12">
          <h1 className="text-4xl md:text-5xl font-bold mb-4">Learning Modules</h1>
          <p className="text-lg text-muted-foreground">
            Progress through our curated modules from basic Verilog to advanced UVM concepts. 
            Each module includes theory, examples, and hands-on simulations.
          </p>
        </div>

        {/* Modules Grid */}
        <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-6">
          {modules.map((module) => (
            <Card key={module.id} className="border-border hover:shadow-glow transition-all duration-300 hover:-translate-y-1 flex flex-col">
              <CardHeader>
                <div className="flex items-start justify-between mb-2">
                  <div className="w-10 h-10 rounded-lg bg-primary/10 flex items-center justify-center">
                    <Code className="w-5 h-5 text-primary" />
                  </div>
                  {module.completed && (
                    <CheckCircle className="w-5 h-5 text-green-500" />
                  )}
                </div>
                <div className="space-y-1">
                  <div className="text-sm text-muted-foreground font-mono">Module {module.id}</div>
                  <CardTitle className="text-xl">{module.title}</CardTitle>
                </div>
                <CardDescription>{module.description}</CardDescription>
              </CardHeader>
              <CardContent className="flex-1 flex flex-col justify-between">
                <div className="space-y-4">
                  <Badge variant="outline" className={getDifficultyColor(module.difficulty)}>
                    {module.difficulty}
                  </Badge>
                  <div className="flex flex-wrap gap-2">
                    {module.topics.map((topic, index) => (
                      <Badge key={index} variant="secondary" className="text-xs">
                        {topic}
                      </Badge>
                    ))}
                  </div>
                </div>
                <div className="flex gap-2 mt-6">
                  <Button variant="default" className="flex-1" asChild>
                    <a href={`/modules/${module.id}`}>Start Module</a>
                  </Button>
                  <Button variant="outline" size="icon" asChild>
                    <a 
                      href="https://www.edaplayground.com/" 
                      target="_blank" 
                      rel="noopener noreferrer"
                      aria-label="Open in EDA Playground"
                    >
                      <ExternalLink className="w-4 h-4" />
                    </a>
                  </Button>
                </div>
              </CardContent>
            </Card>
          ))}
        </div>

        {/* Bottom CTA */}
        <div className="mt-16 p-8 bg-gradient-card rounded-lg border border-border text-center">
          <h3 className="text-2xl font-bold mb-2">Want to Add a Module?</h3>
          <p className="text-muted-foreground mb-4">
            Contributions are welcome! Share your knowledge with the community.
          </p>
          <Button asChild variant="default">
            <a href="https://github.com/chiplearn" target="_blank" rel="noopener noreferrer">
              Contribute on GitHub
            </a>
          </Button>
        </div>
      </div>
    </div>
  );
};

export default Modules;
