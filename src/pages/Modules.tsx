import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Badge } from "@/components/ui/badge";
import { Code, ExternalLink, CheckCircle } from "lucide-react";
import { useState, useEffect } from "react";
interface Module {
  id: string;
  slug: string;
  title: string;
  description: string;
  difficulty: string;
  topics: string[];
  completed: boolean;
}
const Modules = () => {
  const [modules, setModules] = useState<Module[]>([]);
  const [loading, setLoading] = useState(true);
  useEffect(() => {
    fetch('/modules.json').then(res => res.json()).then(data => {
      setModules(data.modules);
      setLoading(false);
    }).catch(error => {
      console.error('Error loading modules:', error);
      setLoading(false);
    });
  }, []);
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
  return <div className="min-h-screen py-20">
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
        {loading ? <div className="text-center py-12">
            <p className="text-muted-foreground">Loading modules...</p>
          </div> : <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-6">
            {modules.map(module => <Card key={module.id} className="border-border hover:shadow-glow transition-all duration-300 hover:-translate-y-1 flex flex-col">
              
              <CardContent className="flex-1 flex flex-col justify-between">
                <div className="space-y-4">
                  <Badge variant="outline" className={getDifficultyColor(module.difficulty)}>
                    {module.difficulty}
                  </Badge>
                  <div className="flex flex-wrap gap-2">
                    {module.topics.map((topic, index) => <Badge key={index} variant="secondary" className="text-xs">
                        {topic}
                      </Badge>)}
                  </div>
                </div>
                <div className="flex gap-2 mt-6">
                  <Button variant="default" className="flex-1" asChild>
                    <a href={`/modules/${module.slug}`}>Start Module</a>
                  </Button>
                  <Button variant="outline" size="icon" asChild>
                    <a href="https://www.edaplayground.com/" target="_blank" rel="noopener noreferrer" aria-label="Open in EDA Playground">
                      <ExternalLink className="w-4 h-4" />
                    </a>
                  </Button>
                </div>
              </CardContent>
            </Card>)}
          </div>}

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
    </div>;
};
export default Modules;