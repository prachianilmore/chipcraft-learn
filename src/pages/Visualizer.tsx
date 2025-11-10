import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Activity, FileCode, Play } from "lucide-react";

const Visualizer = () => {
  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4">
        {/* Header */}
        <div className="max-w-3xl mb-12">
          <h1 className="text-4xl md:text-5xl font-bold mb-4">Waveform Visualizer</h1>
          <p className="text-lg text-muted-foreground">
            Visualize signal behavior, debug timing issues, and understand your hardware designs through interactive waveforms.
          </p>
        </div>

        {/* Main Visualizer Area */}
        <Card className="mb-8">
          <CardHeader>
            <CardTitle>Simulation Viewer</CardTitle>
            <CardDescription>
              Connect to EDA Playground to view live simulation waveforms
            </CardDescription>
          </CardHeader>
          <CardContent>
            <div className="aspect-video bg-secondary rounded-lg border-2 border-dashed border-border flex items-center justify-center">
              <div className="text-center space-y-4">
                <Activity className="w-16 h-16 text-muted-foreground mx-auto" />
                <div>
                  <p className="text-lg font-semibold mb-2">No Active Simulation</p>
                  <p className="text-muted-foreground mb-4">
                    Run a simulation from the Modules page or EDA Playground to see waveforms here
                  </p>
                  <Button asChild>
                    <a href="https://www.edaplayground.com/" target="_blank" rel="noopener noreferrer">
                      Open EDA Playground
                    </a>
                  </Button>
                </div>
              </div>
            </div>
          </CardContent>
        </Card>

        {/* Example Waveforms Grid */}
        <div>
          <h2 className="text-2xl font-bold mb-6">Example Waveforms</h2>
          <div className="grid md:grid-cols-2 gap-6">
            {[
              {
                title: "4-bit Counter",
                description: "Synchronous up counter with reset",
                icon: FileCode,
              },
              {
                title: "FSM Traffic Light",
                description: "State machine with timing diagram",
                icon: Play,
              },
              {
                title: "8-bit Adder",
                description: "Combinational logic propagation",
                icon: Activity,
              },
              {
                title: "UART Transmitter",
                description: "Serial communication timing",
                icon: FileCode,
              },
            ].map((example, index) => (
              <Card key={index} className="border-border hover:shadow-medium transition-shadow">
                <CardHeader>
                  <div className="flex items-center gap-3 mb-2">
                    <div className="w-10 h-10 rounded-lg bg-accent/10 flex items-center justify-center">
                      <example.icon className="w-5 h-5 text-accent" />
                    </div>
                    <CardTitle className="text-lg">{example.title}</CardTitle>
                  </div>
                  <CardDescription>{example.description}</CardDescription>
                </CardHeader>
                <CardContent>
                  <div className="aspect-video bg-gradient-card rounded border border-border flex items-center justify-center text-muted-foreground">
                    <span className="text-sm">Waveform Preview</span>
                  </div>
                  <Button variant="outline" className="w-full mt-4">
                    View Example
                  </Button>
                </CardContent>
              </Card>
            ))}
          </div>
        </div>

        {/* Info Section */}
        <div className="mt-16 p-8 bg-secondary rounded-lg border border-border">
          <h3 className="text-xl font-bold mb-4">About the Visualizer</h3>
          <div className="space-y-2 text-muted-foreground">
            <p>
              The ChipLearn Visualizer helps you understand how digital signals change over time. 
              By examining waveforms, you can:
            </p>
            <ul className="list-disc list-inside space-y-1 ml-4">
              <li>Debug timing issues in sequential circuits</li>
              <li>Verify correct operation of state machines</li>
              <li>Understand signal propagation delays</li>
              <li>Validate testbench assertions</li>
            </ul>
            <p className="pt-4">
              Integration with EDA Playground allows you to run simulations and view results 
              directly in your browser without any local setup.
            </p>
          </div>
        </div>
      </div>
    </div>
  );
};

export default Visualizer;
