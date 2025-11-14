import { Button } from "@/components/ui/button";
import { Card, CardContent } from "@/components/ui/card";
import { Code, Zap, Users, BookOpen } from "lucide-react";
import { Link } from "react-router-dom";

const Home = () => {
  const features = [
    {
      icon: BookOpen,
      title: "Interactive Lessons",
      description: "Learn Verilog, SystemVerilog, and UVM through hands-on, bite-sized modules",
    },
    {
      icon: Code,
      title: "Real Simulations",
      description: "Run actual HDL simulations directly in your browser with EDA Playground",
    },
    {
      icon: Zap,
      title: "Instant Feedback",
      description: "See waveforms, debug your code, and understand hardware behavior in real-time",
    },
    {
      icon: Users,
      title: "Community Driven",
      description: "Contribute modules, share knowledge, and grow with fellow learners",
    },
  ];

  return (
    <div className="min-h-screen">
      {/* Hero Section */}
      <section className="relative overflow-hidden bg-gradient-hero text-primary-foreground">
        <div className="absolute inset-0 bg-[url('data:image/svg+xml;base64,PHN2ZyB3aWR0aD0iNjAiIGhlaWdodD0iNjAiIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyI+PGRlZnM+PHBhdHRlcm4gaWQ9ImdyaWQiIHdpZHRoPSI2MCIgaGVpZ2h0PSI2MCIgcGF0dGVyblVuaXRzPSJ1c2VyU3BhY2VPblVzZSI+PHBhdGggZD0iTSAxMCAwIEwgMCAwIDAgMTAiIGZpbGw9Im5vbmUiIHN0cm9rZT0id2hpdGUiIHN0cm9rZS1vcGFjaXR5PSIwLjA1IiBzdHJva2Utd2lkdGg9IjEiLz48L3BhdHRlcm4+PC9kZWZzPjxyZWN0IHdpZHRoPSIxMDAlIiBoZWlnaHQ9IjEwMCUiIGZpbGw9InVybCgjZ3JpZCkiLz48L3N2Zz4=')] opacity-20"></div>
        <div className="container mx-auto px-4 py-20 md:py-32 relative">
          <div className="max-w-3xl mx-auto text-center space-y-6">
            <h1 className="text-4xl md:text-6xl font-bold tracking-tight animate-fade-in">
              Learn, Simulate, and Verify Hardware Designs
            </h1>
            <p className="text-lg md:text-xl text-primary-foreground/90 animate-fade-in">
              Master digital design and hardware verification through interactive lessons, 
              real simulations, and hands-on practice. From Verilog basics to advanced UVM concepts.
            </p>
            <div className="flex flex-col sm:flex-row gap-4 justify-center pt-4 animate-fade-in">
              <Button asChild size="lg" variant="secondary" className="text-lg">
                <Link to="/modules">Start Learning</Link>
              </Button>
            <Button asChild size="lg" variant="outline" className="text-lg border-primary-foreground hover:bg-primary-foreground hover:text-primary text-primary-foreground">
              <Link to="/about">Learn More</Link>
            </Button>
            </div>
          </div>
        </div>
      </section>

      {/* Features Section */}
      <section className="py-20">
        <div className="container mx-auto px-4">
          <div className="text-center mb-12">
            <h2 className="text-3xl md:text-4xl font-bold mb-4">Why ChipLearn?</h2>
            <p className="text-lg text-muted-foreground max-w-2xl mx-auto">
              Democratizing chip design verification education through open-source collaboration
            </p>
          </div>
          <div className="grid md:grid-cols-2 lg:grid-cols-4 gap-6">
            {features.map((feature, index) => (
              <Card 
                key={index} 
                className="border-border hover:shadow-glow transition-all duration-300 hover:-translate-y-1"
              >
                <CardContent className="p-6 space-y-4">
                  <div className="w-12 h-12 rounded-lg bg-accent/10 flex items-center justify-center">
                    <feature.icon className="w-6 h-6 text-accent" />
                  </div>
                  <h3 className="text-xl font-semibold">{feature.title}</h3>
                  <p className="text-muted-foreground">{feature.description}</p>
                </CardContent>
              </Card>
            ))}
          </div>
        </div>
      </section>

      {/* CTA Section */}
      <section className="py-20 bg-secondary">
        <div className="container mx-auto px-4">
          <div className="max-w-3xl mx-auto text-center space-y-6">
            <h2 className="text-3xl md:text-4xl font-bold">Ready to Start Your Journey?</h2>
            <p className="text-lg text-muted-foreground">
              Join our growing community of learners and contributors. Begin with fundamentals 
              or dive into advanced verification concepts.
            </p>
            <Button asChild size="lg" className="text-lg">
              <Link to="/modules">Explore Modules</Link>
            </Button>
          </div>
        </div>
      </section>
    </div>
  );
};

export default Home;
