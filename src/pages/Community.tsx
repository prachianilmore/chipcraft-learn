import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { GitFork, GitPullRequest, Github, MessageSquare, Users } from "lucide-react";

const Community = () => {
  const steps = [
    {
      number: "01",
      icon: GitFork,
      title: "Fork the Repository",
      description: "Start by forking the ChipLearn repository to your GitHub account",
    },
    {
      number: "02",
      icon: GitPullRequest,
      title: "Add Your Module",
      description: "Create a new module with examples, explanations, and test cases",
    },
    {
      number: "03",
      icon: MessageSquare,
      title: "Submit a Pull Request",
      description: "Open a PR with your changes and describe what you've added",
    },
    {
      number: "04",
      icon: Users,
      title: "Collaborate & Review",
      description: "Work with maintainers to refine and merge your contribution",
    },
  ];

  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4">
        {/* Header */}
        <div className="max-w-3xl mx-auto text-center mb-16">
          <h1 className="text-4xl md:text-5xl font-bold mb-4">Join Our Community</h1>
          <p className="text-lg text-muted-foreground">
            ChipLearn thrives on contributions from learners and educators worldwide. 
            Share your knowledge, improve existing content, and help democratize chip design education.
          </p>
        </div>

        {/* Contribution Steps */}
        <div className="mb-16">
          <h2 className="text-3xl font-bold text-center mb-12">How to Contribute</h2>
          <div className="grid md:grid-cols-2 gap-6 max-w-5xl mx-auto">
            {steps.map((step) => (
              <Card key={step.number} className="border-border hover:shadow-glow transition-all duration-300">
                <CardHeader>
                  <div className="flex items-center gap-4 mb-2">
                    <div className="w-12 h-12 rounded-full bg-primary text-primary-foreground flex items-center justify-center font-bold text-lg">
                      {step.number}
                    </div>
                    <div className="w-10 h-10 rounded-lg bg-accent/10 flex items-center justify-center">
                      <step.icon className="w-5 h-5 text-accent" />
                    </div>
                  </div>
                  <CardTitle>{step.title}</CardTitle>
                  <CardDescription className="text-base">{step.description}</CardDescription>
                </CardHeader>
              </Card>
            ))}
          </div>
        </div>

        {/* What to Contribute */}
        <div className="mb-16">
          <h2 className="text-3xl font-bold text-center mb-8">What Can You Contribute?</h2>
          <div className="grid md:grid-cols-3 gap-6 max-w-5xl mx-auto">
            {[
              {
                title: "New Modules",
                description: "Create lessons on topics you're passionate about",
                examples: ["Memory designs", "Protocol implementations", "Advanced verification"],
              },
              {
                title: "Code Examples",
                description: "Share working code snippets and testbenches",
                examples: ["Real-world designs", "Common patterns", "Best practices"],
              },
              {
                title: "Improvements",
                description: "Enhance existing content and fix issues",
                examples: ["Better explanations", "Bug fixes", "Updated examples"],
              },
            ].map((item, index) => (
              <Card key={index} className="border-border">
                <CardHeader>
                  <CardTitle className="text-xl">{item.title}</CardTitle>
                  <CardDescription>{item.description}</CardDescription>
                </CardHeader>
                <CardContent>
                  <ul className="space-y-2">
                    {item.examples.map((example, i) => (
                      <li key={i} className="flex items-center gap-2 text-sm text-muted-foreground">
                        <span className="w-1.5 h-1.5 rounded-full bg-accent"></span>
                        {example}
                      </li>
                    ))}
                  </ul>
                </CardContent>
              </Card>
            ))}
          </div>
        </div>

        {/* CTA Section */}
        <div className="bg-gradient-hero text-primary-foreground rounded-lg p-8 md:p-12 text-center">
          <h2 className="text-3xl font-bold mb-4">Ready to Make an Impact?</h2>
          <p className="text-lg mb-6 max-w-2xl mx-auto opacity-90">
            Your contribution can help thousands of learners worldwide understand chip design better. 
            Every module, example, and improvement matters.
          </p>
          <div className="flex flex-col sm:flex-row gap-4 justify-center">
            <Button asChild size="lg" variant="secondary">
              <a href="https://github.com/chiplearn" target="_blank" rel="noopener noreferrer" className="gap-2">
                <Github className="w-5 h-5" />
                Contribute on GitHub
              </a>
            </Button>
            <Button asChild size="lg" variant="outline" className="border-primary-foreground/30 hover:bg-primary-foreground/10 text-primary-foreground">
              <a href="https://github.com/chiplearn/discussions" target="_blank" rel="noopener noreferrer">
                Join Discussions
              </a>
            </Button>
          </div>
        </div>

        {/* Guidelines */}
        <div className="mt-16 max-w-3xl mx-auto">
          <h3 className="text-2xl font-bold mb-4">Contribution Guidelines</h3>
          <Card>
            <CardContent className="pt-6 space-y-3 text-muted-foreground">
              <p>• <strong>Quality First:</strong> Ensure your code is well-commented and follows best practices</p>
              <p>• <strong>Clear Documentation:</strong> Explain concepts in simple terms with practical examples</p>
              <p>• <strong>Test Your Work:</strong> Verify simulations run correctly on EDA Playground</p>
              <p>• <strong>Be Respectful:</strong> Maintain a welcoming and inclusive environment</p>
              <p>• <strong>Stay Organized:</strong> Follow the existing module structure and naming conventions</p>
            </CardContent>
          </Card>
        </div>
      </div>
    </div>
  );
};

export default Community;
