import { Card, CardContent } from "@/components/ui/card";
import { BookOpen, Target, Heart, Zap } from "lucide-react";

const About = () => {
  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4 max-w-4xl">
        {/* Header */}
        <div className="text-center mb-16">
          <h1 className="text-4xl md:text-5xl font-bold mb-4">About ChipLearn</h1>
          <p className="text-xl text-muted-foreground">
            Democratizing chip design verification education through open collaboration
          </p>
        </div>

        {/* Mission Section */}
        <div className="mb-16">
          <div className="flex items-center gap-3 mb-6">
            <div className="w-12 h-12 rounded-lg bg-primary/10 flex items-center justify-center">
              <Target className="w-6 h-6 text-primary" />
            </div>
            <h2 className="text-3xl font-bold">Our Mission</h2>
          </div>
          <Card className="border-border">
            <CardContent className="pt-6 space-y-4 text-lg text-muted-foreground">
              <p>
                ChipLearn was created to make hardware design and verification education accessible to everyone, 
                regardless of their background or resources. We believe that learning chip design shouldn't 
                require expensive tools or complex setups.
              </p>
              <p>
                By leveraging EDA Playground and open-source collaboration, we provide a hands-on, interactive 
                learning experience that bridges the gap between theory and practice. Our goal is to empower 
                the next generation of chip designers and verification engineers.
              </p>
            </CardContent>
          </Card>
        </div>

        {/* What Makes Us Different */}
        <div className="mb-16">
          <h2 className="text-3xl font-bold mb-8">What Makes ChipLearn Different</h2>
          <div className="grid md:grid-cols-2 gap-6">
            {[
              {
                icon: BookOpen,
                title: "Learn by Doing",
                description: "Every concept is paired with runnable code examples and real simulations, not just theory.",
              },
              {
                icon: Zap,
                title: "Zero Setup Required",
                description: "Start learning immediately with browser-based simulations. No installations, no license hassles.",
              },
              {
                icon: Heart,
                title: "Community Driven",
                description: "Built by learners, for learners. Every module can be improved through open contributions.",
              },
              {
                icon: Target,
                title: "Industry Relevant",
                description: "Focus on practical skills used in real chip verification roles, from RTL to UVM.",
              },
            ].map((item, index) => (
              <Card key={index} className="border-border">
                <CardContent className="pt-6">
                  <div className="flex items-start gap-4">
                    <div className="w-10 h-10 rounded-lg bg-accent/10 flex items-center justify-center flex-shrink-0">
                      <item.icon className="w-5 h-5 text-accent" />
                    </div>
                    <div>
                      <h3 className="text-xl font-semibold mb-2">{item.title}</h3>
                      <p className="text-muted-foreground">{item.description}</p>
                    </div>
                  </div>
                </CardContent>
              </Card>
            ))}
          </div>
        </div>

        {/* Stakeholders */}
        <div className="mb-16">
          <h2 className="text-3xl font-bold mb-6">Built With Support From</h2>
          <Card className="border-border bg-gradient-card">
            <CardContent className="pt-6 space-y-6">
              <div>
                <h3 className="text-xl font-semibold mb-2">Community Dreams Foundation (CDF)</h3>
                <p className="text-muted-foreground">
                  The Community Dreams Foundation sponsors this initiative as part of their mission to 
                  provide quality education and opportunities to underserved communities. Their support 
                  makes it possible to keep ChipLearn free and accessible.
                </p>
              </div>
              <div>
                <h3 className="text-xl font-semibold mb-2">Open Education Team</h3>
                <p className="text-muted-foreground">
                  A dedicated group of engineers, educators, and students who volunteer their time to 
                  create, review, and maintain learning content. Together, we're building a resource 
                  that empowers learners worldwide.
                </p>
              </div>
              <div>
                <h3 className="text-xl font-semibold mb-2">EDA Playground</h3>
                <p className="text-muted-foreground">
                  Our simulation platform partner that makes browser-based HDL simulation possible. 
                  Their technology enables instant hands-on practice without requiring any software installation.
                </p>
              </div>
            </CardContent>
          </Card>
        </div>
        {/* Content & Curriculum */}
        <div className="mb-16">
          <h2 className="text-2xl font-bold mb-3">Content & Curriculum</h2>
          <p className="text-muted-foreground">
            The learning content and curriculum for ChipLearn have been authored and maintained by Prachi Anil More.
          </p>
        </div>

        {/* Get Involved */}
        <div className="bg-secondary rounded-lg p-8 text-center">
          <h2 className="text-2xl font-bold mb-4">Get Involved</h2>
          <p className="text-muted-foreground mb-6 max-w-2xl mx-auto">
            ChipLearn is built by people like you. Whether you're a student, professional engineer, 
            or educator, your contribution can help shape the future of hardware design education.
          </p>
          <div className="flex flex-col sm:flex-row gap-4 justify-center">
            <a
              href="https://github.com/chiplearn"
              target="_blank"
              rel="noopener noreferrer"
              className="inline-flex items-center justify-center px-6 py-3 rounded-lg bg-primary text-primary-foreground font-medium hover:opacity-90 transition-opacity"
            >
              Contribute on GitHub
            </a>
            <a
              href="/community"
              className="inline-flex items-center justify-center px-6 py-3 rounded-lg border border-border font-medium hover:bg-accent/10 transition-colors"
            >
              Learn How to Contribute
            </a>
          </div>
        </div>
      </div>
    </div>
  );
};

export default About;
