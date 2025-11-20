import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Github, Code2, FileText, Users } from "lucide-react";

const Community = () => {
  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4">
        {/* Header */}
        <div className="max-w-3xl mx-auto text-center mb-16">
          <h1 className="text-4xl md:text-5xl font-bold mb-4">Contribute Your Code Examples</h1>
          <p className="text-lg text-muted-foreground">
            ChipLearn is a collaborative platform, and you can contribute by sharing Verilog, SystemVerilog, 
            and UVM example projects that help learners explore real designs and verification patterns.
          </p>
        </div>

        {/* How to Contribute */}
        <div className="mb-16">
          <h2 className="text-3xl font-bold text-center mb-12">How to Contribute</h2>
          <div className="max-w-3xl mx-auto">
            <Card className="border-border">
              <CardContent className="pt-6">
                <ol className="space-y-4">
                  <li className="flex gap-4">
                    <div className="w-8 h-8 rounded-full bg-primary text-primary-foreground flex items-center justify-center font-bold flex-shrink-0">
                      1
                    </div>
                    <div>
                      <p className="font-semibold text-foreground">Fork the GitHub repository</p>
                    </div>
                  </li>
                  <li className="flex gap-4">
                    <div className="w-8 h-8 rounded-full bg-primary text-primary-foreground flex items-center justify-center font-bold flex-shrink-0">
                      2
                    </div>
                    <div>
                      <p className="font-semibold text-foreground">Add your example inside <code className="text-accent">/community-projects</code></p>
                    </div>
                  </li>
                  <li className="flex gap-4">
                    <div className="w-8 h-8 rounded-full bg-primary text-primary-foreground flex items-center justify-center font-bold flex-shrink-0">
                      3
                    </div>
                    <div>
                      <p className="font-semibold text-foreground">Include your RTL, testbench, or UVM component</p>
                    </div>
                  </li>
                  <li className="flex gap-4">
                    <div className="w-8 h-8 rounded-full bg-primary text-primary-foreground flex items-center justify-center font-bold flex-shrink-0">
                      4
                    </div>
                    <div>
                      <p className="font-semibold text-foreground">Add a simple README.md explaining what your example does</p>
                    </div>
                  </li>
                  <li className="flex gap-4">
                    <div className="w-8 h-8 rounded-full bg-primary text-primary-foreground flex items-center justify-center font-bold flex-shrink-0">
                      5
                    </div>
                    <div>
                      <p className="font-semibold text-foreground">Submit a Pull Request for review</p>
                    </div>
                  </li>
                </ol>
              </CardContent>
            </Card>
          </div>
        </div>

        {/* Examples You Can Contribute */}
        <div className="mb-16">
          <h2 className="text-3xl font-bold text-center mb-8">Examples You Can Contribute</h2>
          <div className="grid md:grid-cols-2 gap-6 max-w-4xl mx-auto">
            <Card className="border-border">
              <CardHeader>
                <div className="flex items-center gap-3 mb-2">
                  <div className="w-10 h-10 rounded-lg bg-accent/10 flex items-center justify-center">
                    <Code2 className="w-5 h-5 text-accent" />
                  </div>
                  <CardTitle className="text-xl">Verilog RTL Designs</CardTitle>
                </div>
                <CardDescription>
                  FIFOs, counters, ALUs, state machines
                </CardDescription>
              </CardHeader>
            </Card>

            <Card className="border-border">
              <CardHeader>
                <div className="flex items-center gap-3 mb-2">
                  <div className="w-10 h-10 rounded-lg bg-accent/10 flex items-center justify-center">
                    <FileText className="w-5 h-5 text-accent" />
                  </div>
                  <CardTitle className="text-xl">SystemVerilog Testbenches</CardTitle>
                </div>
                <CardDescription>
                  Testbenches or interface concepts
                </CardDescription>
              </CardHeader>
            </Card>

            <Card className="border-border">
              <CardHeader>
                <div className="flex items-center gap-3 mb-2">
                  <div className="w-10 h-10 rounded-lg bg-accent/10 flex items-center justify-center">
                    <Users className="w-5 h-5 text-accent" />
                  </div>
                  <CardTitle className="text-xl">UVM Components</CardTitle>
                </div>
                <CardDescription>
                  Sequence items, drivers, monitors, or small verification components
                </CardDescription>
              </CardHeader>
            </Card>

            <Card className="border-border">
              <CardHeader>
                <div className="flex items-center gap-3 mb-2">
                  <div className="w-10 h-10 rounded-lg bg-accent/10 flex items-center justify-center">
                    <Code2 className="w-5 h-5 text-accent" />
                  </div>
                  <CardTitle className="text-xl">Design Experiments</CardTitle>
                </div>
                <CardDescription>
                  Helpful design or verification experiments
                </CardDescription>
              </CardHeader>
            </Card>
          </div>
        </div>

        {/* Why This Matters */}
        <div className="bg-gradient-hero text-primary-foreground rounded-lg p-8 md:p-12 text-center">
          <h2 className="text-3xl font-bold mb-4">Why This Matters</h2>
          <p className="text-lg mb-6 max-w-2xl mx-auto opacity-90">
            Community examples help expand ChipLearn with practical, real-world resources that support all learners.
          </p>
          <Button asChild size="lg" variant="secondary">
            <a href="https://github.com/prachianilmore/ChipLearn_CDF" target="_blank" rel="noopener noreferrer" className="gap-2">
              <Github className="w-5 h-5" />
              Contribute on GitHub
            </a>
          </Button>
        </div>
      </div>
    </div>
  );
};

export default Community;
