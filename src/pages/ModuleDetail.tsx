import { useParams, useNavigate } from "react-router-dom";
import { Button } from "@/components/ui/button";
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { Separator } from "@/components/ui/separator";
import { ArrowLeft, ExternalLink, Code, FileText, HelpCircle } from "lucide-react";

const ModuleDetail = () => {
  const { slug } = useParams();
  const navigate = useNavigate();

  // Module data template - to be filled by contributors
  const modulesData: Record<string, any> = {
    "verilog-basics": {
      id: "01",
      title: "Verilog Basics",
      description: "To be added by contributor",
      difficulty: "Beginner",
      topics: ["TODO: Topic 1", "TODO: Topic 2", "TODO: Topic 3"],
      concept: "TODO: Add concept explanation here",
      exampleCode: `// TODO: Add SystemVerilog/Verilog code example
module example_module (
  input wire clk,
  input wire reset,
  output wire out
);
  // TODO: Add implementation
endmodule

// TODO: Add testbench
module tb_example;
  // TODO: Add testbench code
endmodule`,
      expectedOutput: "TODO: Describe expected simulation output",
      quiz: [
        { question: "TODO: Add question 1", answer: "TODO: Add answer 1" },
        { question: "TODO: Add question 2", answer: "TODO: Add answer 2" }
      ]
    },
    "counters-and-fsms": {
      id: "02",
      title: "Counters and FSMs",
      description: "To be added by contributor",
      difficulty: "Beginner",
      topics: ["TODO: Topic 1", "TODO: Topic 2", "TODO: Topic 3"],
      concept: "TODO: Add concept explanation here",
      exampleCode: `// TODO: Add code example`,
      expectedOutput: "TODO: Describe expected simulation output",
      quiz: [
        { question: "TODO: Add question 1", answer: "TODO: Add answer 1" },
        { question: "TODO: Add question 2", answer: "TODO: Add answer 2" }
      ]
    },
    "combinational-circuits": {
      id: "03",
      title: "Combinational Circuits",
      description: "To be added by contributor",
      difficulty: "Intermediate",
      topics: ["TODO: Topic 1", "TODO: Topic 2", "TODO: Topic 3"],
      concept: "TODO: Add concept explanation here",
      exampleCode: `// TODO: Add code example`,
      expectedOutput: "TODO: Describe expected simulation output",
      quiz: [
        { question: "TODO: Add question 1", answer: "TODO: Add answer 1" },
        { question: "TODO: Add question 2", answer: "TODO: Add answer 2" }
      ]
    },
    "systemverilog-fundamentals": {
      id: "04",
      title: "SystemVerilog Fundamentals",
      description: "To be added by contributor",
      difficulty: "Intermediate",
      topics: ["TODO: Topic 1", "TODO: Topic 2", "TODO: Topic 3"],
      concept: "TODO: Add concept explanation here",
      exampleCode: `// TODO: Add code example`,
      expectedOutput: "TODO: Describe expected simulation output",
      quiz: [
        { question: "TODO: Add question 1", answer: "TODO: Add answer 1" },
        { question: "TODO: Add question 2", answer: "TODO: Add answer 2" }
      ]
    },
    "uvm-basics": {
      id: "05",
      title: "UVM Basics",
      description: "To be added by contributor",
      difficulty: "Advanced",
      topics: ["TODO: Topic 1", "TODO: Topic 2", "TODO: Topic 3"],
      concept: "TODO: Add concept explanation here",
      exampleCode: `// TODO: Add code example`,
      expectedOutput: "TODO: Describe expected simulation output",
      quiz: [
        { question: "TODO: Add question 1", answer: "TODO: Add answer 1" },
        { question: "TODO: Add question 2", answer: "TODO: Add answer 2" }
      ]
    },
    "advanced-uvm": {
      id: "06",
      title: "Advanced UVM",
      description: "To be added by contributor",
      difficulty: "Advanced",
      topics: ["TODO: Topic 1", "TODO: Topic 2", "TODO: Topic 3"],
      concept: "TODO: Add concept explanation here",
      exampleCode: `// TODO: Add code example`,
      expectedOutput: "TODO: Describe expected simulation output",
      quiz: [
        { question: "TODO: Add question 1", answer: "TODO: Add answer 1" },
        { question: "TODO: Add question 2", answer: "TODO: Add answer 2" }
      ]
    }
  };

  const module = modulesData[slug || "verilog-basics"];

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
        {/* Template Warning */}
        <div className="mb-6 p-4 bg-yellow-50 dark:bg-yellow-900/20 border border-yellow-200 dark:border-yellow-800 rounded-lg">
          <p className="text-yellow-800 dark:text-yellow-200 flex items-center gap-2">
            <span className="text-xl">⚠</span>
            <span className="font-medium">This is a template. Content will be provided by contributors.</span>
          </p>
        </div>

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
              <CardTitle>Concept Summary – TODO</CardTitle>
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
              <CardTitle>Example Code – TODO</CardTitle>
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
          <CardHeader>
            <CardTitle>Simulation Link – TODO</CardTitle>
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
                  <ExternalLink className="mr-2" /> Run Simulation
                </a>
              </Button>
            </div>
          </CardContent>
        </Card>

        {/* 4. Expected Output */}
        <Card className="mb-8">
          <CardHeader>
            <CardTitle>Expected Output – TODO</CardTitle>
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
              <CardTitle>Quiz/Reflection – TODO</CardTitle>
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
