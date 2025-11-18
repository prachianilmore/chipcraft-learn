import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Badge } from "@/components/ui/badge";
import { Code, ArrowRight, BookOpen } from "lucide-react";
import { useNavigate } from "react-router-dom";

const Modules = () => {
  const navigate = useNavigate();

  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4">
        {/* Header */}
        <div className="max-w-3xl mb-12">
          <h1 className="text-4xl md:text-5xl font-bold mb-4">Learning Tracks</h1>
          <p className="text-lg text-muted-foreground">
            Choose a learning track to begin your journey from basic Verilog to advanced verification concepts.
          </p>
        </div>

        {/* Track Cards */}
        <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-6">
          {/* Verilog Track */}
          <Card className="border-border hover:shadow-glow transition-all duration-300 hover:-translate-y-1 flex flex-col">
            <CardHeader>
              <div className="flex items-start justify-between mb-2">
                <div className="w-12 h-12 rounded-lg bg-primary/10 flex items-center justify-center">
                  <Code className="w-6 h-6 text-primary" />
                </div>
                <Badge variant="outline" className="bg-green-500/10 text-green-600 border-green-500/20">
                  Beginner
                </Badge>
              </div>
              <CardTitle className="text-2xl">Verilog Track</CardTitle>
              <CardDescription>
                Master the fundamentals of Verilog HDL, from basic syntax to testbench creation
              </CardDescription>
            </CardHeader>
            <CardContent className="flex-1 flex flex-col justify-between">
              <div className="space-y-4">
                <div className="flex items-center gap-2 text-sm text-muted-foreground">
                  <BookOpen className="w-4 h-4" />
                  <span>4 Modules</span>
                </div>
                <div className="flex flex-wrap gap-2">
                  <Badge variant="secondary" className="text-xs">Module Declaration</Badge>
                  <Badge variant="secondary" className="text-xs">Combinational Logic</Badge>
                  <Badge variant="secondary" className="text-xs">Sequential Logic</Badge>
                  <Badge variant="secondary" className="text-xs">Testbenches</Badge>
                </div>
              </div>
              <Button 
                variant="default" 
                className="w-full mt-6"
                onClick={() => navigate("/verilog-modules")}
              >
                Start Track <ArrowRight className="ml-2 w-4 h-4" />
              </Button>
            </CardContent>
          </Card>

          {/* Placeholder for future tracks */}
          <Card className="border-border border-dashed opacity-50">
            <CardHeader>
              <div className="w-12 h-12 rounded-lg bg-muted flex items-center justify-center mb-2">
                <Code className="w-6 h-6 text-muted-foreground" />
              </div>
              <CardTitle className="text-2xl">More Tracks Coming Soon</CardTitle>
              <CardDescription>
                SystemVerilog and UVM tracks will be available soon
              </CardDescription>
            </CardHeader>
          </Card>
        </div>

        {/* Call to Action */}
        <div className="mt-20 text-center">
          <h2 className="text-2xl font-bold mb-4">Want to contribute?</h2>
          <p className="text-muted-foreground mb-6">
            Help us expand our learning content by contributing on GitHub
          </p>
          <Button variant="outline" asChild>
            <a href="https://github.com" target="_blank" rel="noopener noreferrer">
              View on GitHub <ArrowRight className="ml-2 w-4 h-4" />
            </a>
          </Button>
        </div>
      </div>
    </div>
  );
};

export default Modules;
