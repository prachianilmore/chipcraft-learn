import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Badge } from "@/components/ui/badge";
import {
  Github,
  ExternalLink,
  FolderTree,
  CheckCircle2,
  Shield,
  BarChart3,
  Layers,
  ArrowRight,
  GitFork,
  FileText,
  GitPullRequest,
  FolderPlus,
} from "lucide-react";

const projects = [
  {
    name: "ALU Verification",
    objective: "Verify arithmetic and logic operations with constrained-random stimulus and assertions.",
    tags: ["RTL", "Assertions", "Coverage"],
    difficulty: "Beginner",
    difficultyColor: "bg-emerald-100 text-emerald-700 border-emerald-200",
    github: "https://github.com/prachianilmore/ChipLearn_CDF",
  },
  {
    name: "FIFO Verification",
    objective: "Validate synchronous FIFO behavior including full, empty, overflow, and underflow conditions.",
    tags: ["RTL", "Assertions", "Coverage"],
    difficulty: "Beginner",
    difficultyColor: "bg-emerald-100 text-emerald-700 border-emerald-200",
    github: "https://github.com/prachianilmore/ChipLearn_CDF",
  },
  {
    name: "Arbiter Verification",
    objective: "Test round-robin and priority arbitration with fairness checks and protocol assertions.",
    tags: ["RTL", "Assertions", "Coverage"],
    difficulty: "Intermediate",
    difficultyColor: "bg-amber-100 text-amber-700 border-amber-200",
    github: "https://github.com/prachianilmore/ChipLearn_CDF",
  },
  {
    name: "Register File Verification",
    objective: "Verify read/write access, port conflicts, and reset behavior of a multi-port register file.",
    tags: ["RTL", "Assertions", "Coverage"],
    difficulty: "Intermediate",
    difficultyColor: "bg-amber-100 text-amber-700 border-amber-200",
    github: "https://github.com/prachianilmore/ChipLearn_CDF",
  },
  {
    name: "Handshake Protocol Verification",
    objective: "Validate valid-ready handshake timing, backpressure, and data integrity across interfaces.",
    tags: ["RTL", "Assertions", "Coverage"],
    difficulty: "Advanced",
    difficultyColor: "bg-red-100 text-red-700 border-red-200",
    github: "https://github.com/prachianilmore/ChipLearn_CDF",
  },
  {
    name: "Mini UVM Environment",
    objective: "Build a reusable UVM testbench with driver, monitor, scoreboard, and functional coverage.",
    tags: ["RTL", "Assertions", "Coverage", "UVM"],
    difficulty: "Advanced",
    difficultyColor: "bg-red-100 text-red-700 border-red-200",
    github: "https://github.com/prachianilmore/ChipLearn_CDF",
  },
];

const philosophyItems = [
  { icon: Shield, label: "Verification-first thinking", color: "border-l-blue-400" },
  { icon: CheckCircle2, label: "Self-checking environments", color: "border-l-emerald-400" },
  { icon: Layers, label: "Assertion-based verification", color: "border-l-purple-400" },
  { icon: BarChart3, label: "Coverage-driven validation", color: "border-l-amber-400" },
  { icon: ArrowRight, label: "Progressive complexity", color: "border-l-cyan-400" },
];

const contributionSteps = [
  { icon: GitFork, text: "Fork the repository" },
  { icon: FolderPlus, text: "Add your project following the standard structure" },
  { icon: FileText, text: "Include README with objectives and verification strategy" },
  { icon: GitPullRequest, text: "Submit a pull request" },
];

const Community = () => {
  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4">
        {/* Header */}
        <div className="max-w-3xl mx-auto text-center mb-16">
          <h1 className="text-4xl md:text-5xl font-bold mb-4">Design & Verification Lab</h1>
          <p className="text-lg text-muted-foreground mb-3">
            A structured roadmap of RTL design and verification projects hosted on GitHub.
            Each project emphasizes verification-first thinking, self-checking environments, assertions, coverage, and industry-style organization.
          </p>
          <p className="text-sm text-muted-foreground">
            This lab serves as a practical, portfolio-ready collection of progressive design and verification exercises.
          </p>
        </div>

        {/* Project Roadmap */}
        <section className="mb-20">
          <div className="mb-8">
            <h2 className="text-2xl font-bold tracking-tight uppercase text-foreground">Project Roadmap</h2>
            <div className="h-[2px] w-24 bg-gradient-to-r from-blue-400/60 to-transparent mt-2" />
          </div>
          <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-6">
            {projects.map((project, index) => (
              <Card
                key={project.name}
                className="border-border border-l-[3px] border-l-blue-400/60 bg-card hover:-translate-y-0.5 hover:shadow-[var(--shadow-medium)] transition-all duration-200 flex flex-col"
                style={{ boxShadow: "var(--shadow-subtle)" }}
              >
                <CardHeader className="pb-3">
                  <div className="flex items-center justify-between mb-2">
                    <span className="text-xs font-semibold text-muted-foreground tracking-wide uppercase">
                      Project {String(index + 1).padStart(2, "0")}
                    </span>
                    <Badge className={`text-[10px] font-semibold border ${project.difficultyColor}`}>
                      {project.difficulty}
                    </Badge>
                  </div>
                  <CardTitle className="text-lg">{project.name}</CardTitle>
                </CardHeader>
                <CardContent className="flex flex-col flex-1 pt-0">
                  <p className="text-sm text-muted-foreground mb-4 flex-1">{project.objective}</p>
                  <div className="flex flex-wrap gap-1.5 mb-5">
                    {project.tags.map((tag) => (
                      <Badge key={tag} variant="secondary" className="text-[10px] font-medium">
                        {tag}
                      </Badge>
                    ))}
                  </div>
                  <Button asChild size="sm" className="w-full gap-2">
                    <a href={project.github} target="_blank" rel="noopener noreferrer">
                      <Github className="w-4 h-4" />
                      View on GitHub
                      <ExternalLink className="w-3 h-3 ml-auto" />
                    </a>
                  </Button>
                </CardContent>
              </Card>
            ))}
          </div>
        </section>

        {/* Standard Project Structure */}
        <section className="mb-20">
          <div className="mb-8">
            <h2 className="text-2xl font-bold tracking-tight uppercase text-foreground">Standard Project Structure</h2>
            <div className="h-[2px] w-24 bg-gradient-to-r from-purple-400/60 to-transparent mt-2" />
          </div>
          <div className="max-w-2xl">
            <Card className="border-border border-l-[3px] border-l-purple-400/60" style={{ boxShadow: "var(--shadow-subtle)" }}>
              <CardContent className="pt-6">
                <div className="flex items-center gap-2 mb-4 text-muted-foreground">
                  <FolderTree className="w-5 h-5" />
                  <span className="text-sm font-semibold uppercase tracking-wide">Folder Layout</span>
                </div>
                <pre className="bg-muted/50 rounded-lg p-5 text-sm font-mono text-foreground leading-relaxed overflow-x-auto">
{`project_name/
├── rtl/
├── tb/
├── assertions/
├── coverage/
├── sim/
└── README.md`}
                </pre>
                <p className="text-sm text-muted-foreground mt-4">
                  All lab projects follow a consistent structure to ensure clarity, maintainability, and interview-ready organization.
                </p>
              </CardContent>
            </Card>
          </div>
        </section>

        {/* Verification Philosophy */}
        <section className="mb-20">
          <div className="mb-8">
            <h2 className="text-2xl font-bold tracking-tight uppercase text-foreground">Verification Philosophy</h2>
            <div className="h-[2px] w-24 bg-gradient-to-r from-emerald-400/60 to-transparent mt-2" />
          </div>
          <div className="grid sm:grid-cols-2 lg:grid-cols-3 gap-4">
            {philosophyItems.map((item) => (
              <Card
                key={item.label}
                className={`border-border border-l-[3px] ${item.color} hover:-translate-y-0.5 hover:shadow-[var(--shadow-medium)] transition-all duration-200`}
                style={{ boxShadow: "var(--shadow-subtle)" }}
              >
                <CardContent className="pt-5 pb-5 flex items-center gap-3">
                  <item.icon className="w-5 h-5 text-muted-foreground flex-shrink-0" />
                  <span className="text-sm font-semibold text-foreground">{item.label}</span>
                </CardContent>
              </Card>
            ))}
          </div>
        </section>

        {/* Contribute to the Lab */}
        <section>
          <div className="mb-8">
            <h2 className="text-2xl font-bold tracking-tight uppercase text-foreground">Contribute to the Lab</h2>
            <div className="h-[2px] w-24 bg-gradient-to-r from-amber-400/60 to-transparent mt-2" />
          </div>
          <div className="max-w-2xl">
            <Card className="border-border" style={{ boxShadow: "var(--shadow-subtle)" }}>
              <CardContent className="pt-6">
                <ol className="space-y-4">
                  {contributionSteps.map((step, i) => (
                    <li key={i} className="flex items-start gap-3">
                      <div className="w-7 h-7 rounded-full bg-primary text-primary-foreground flex items-center justify-center text-xs font-bold flex-shrink-0 mt-0.5">
                        {i + 1}
                      </div>
                      <div className="flex items-center gap-2">
                        <step.icon className="w-4 h-4 text-muted-foreground flex-shrink-0" />
                        <span className="text-sm font-medium text-foreground">{step.text}</span>
                      </div>
                    </li>
                  ))}
                </ol>
                <div className="mt-6 pt-4 border-t border-border">
                  <Button asChild variant="outline" size="sm" className="gap-2">
                    <a href="https://github.com/prachianilmore/ChipLearn_CDF" target="_blank" rel="noopener noreferrer">
                      <Github className="w-4 h-4" />
                      Open Repository
                      <ExternalLink className="w-3 h-3" />
                    </a>
                  </Button>
                </div>
              </CardContent>
            </Card>
          </div>
        </section>
      </div>
    </div>
  );
};

export default Community;
