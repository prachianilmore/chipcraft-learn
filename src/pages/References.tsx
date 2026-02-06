import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { BookOpen, FileText, GraduationCap, Wrench, Users, BookMarked, ExternalLink, Lock, CheckCircle } from "lucide-react";

interface BookItemProps {
  href: string;
  title: string;
  description: string;
  accentColor: "green" | "blue" | "purple";
}

const BookItem = ({ href, title, description, accentColor }: BookItemProps) => {
  const colorClasses = {
    green: {
      border: "border-l-emerald-500",
      bg: "bg-emerald-50/50 dark:bg-emerald-950/20",
      hoverBg: "hover:bg-emerald-50 dark:hover:bg-emerald-950/40",
      icon: "text-emerald-600 dark:text-emerald-400",
    },
    blue: {
      border: "border-l-blue-500",
      bg: "bg-blue-50/50 dark:bg-blue-950/20",
      hoverBg: "hover:bg-blue-50 dark:hover:bg-blue-950/40",
      icon: "text-blue-600 dark:text-blue-400",
    },
    purple: {
      border: "border-l-purple-500",
      bg: "bg-purple-50/50 dark:bg-purple-950/20",
      hoverBg: "hover:bg-purple-50 dark:hover:bg-purple-950/40",
      icon: "text-purple-600 dark:text-purple-400",
    },
  };

  const colors = colorClasses[accentColor];

  return (
    <li>
      <a
        href={href}
        target="_blank"
        rel="noopener noreferrer"
        className={`group flex items-start gap-3 p-4 rounded-lg border-l-4 ${colors.border} ${colors.bg} ${colors.hoverBg} transition-all duration-200 hover:shadow-sm hover:translate-x-0.5 cursor-pointer`}
      >
        <BookMarked className={`w-4 h-4 mt-0.5 flex-shrink-0 ${colors.icon}`} />
        <div className="min-w-0">
          <span className="font-semibold text-foreground group-hover:text-primary transition-colors leading-tight block">
            {title}
          </span>
          <p className="text-muted-foreground/80 text-xs mt-1.5 leading-relaxed">
            {description}
          </p>
        </div>
      </a>
    </li>
  );
};

const References = () => {
  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4">
        {/* Header */}
        <div className="max-w-3xl mb-12">
          <h1 className="text-4xl md:text-5xl font-bold mb-4">References</h1>
          <p className="text-lg text-muted-foreground">
            A curated collection of resources to deepen your understanding of Verilog, SystemVerilog, and UVM. 
            Whether you're just starting out or preparing for interviews, these references will help you 
            build a strong foundation in chip design and verification.
          </p>
        </div>

        <div className="space-y-12">
          {/* Books Section */}
          <section>
            <div className="flex items-center gap-3 mb-6">
              <div className="w-10 h-10 rounded-lg bg-primary/10 flex items-center justify-center">
                <BookOpen className="w-5 h-5 text-primary" />
              </div>
              <h2 className="text-2xl font-bold">Books</h2>
            </div>
            
            <div className="grid md:grid-cols-3 gap-6">
              {/* Verilog Books */}
              <Card className="border-border shadow-sm hover:shadow-md transition-shadow duration-200">
                <CardHeader>
                  <div className="flex items-center justify-between mb-2">
                    <CardTitle className="text-lg">Verilog</CardTitle>
                    <Badge variant="outline" className="bg-emerald-500/10 text-emerald-600 border-emerald-500/20">
                      Beginner
                    </Badge>
                  </div>
                  <CardDescription>
                    Essential books for learning Verilog HDL fundamentals
                  </CardDescription>
                </CardHeader>
                <CardContent>
                  <ul className="space-y-3 text-sm">
                    <BookItem
                      href="https://www.amazon.com/dp/0130449113"
                      title="Verilog HDL: A Guide to Digital Design and Synthesis – Samir Palnitkar"
                      description="Industry-standard introduction to Verilog HDL and synthesizable design concepts."
                      accentColor="green"
                    />
                    <BookItem
                      href="https://www.amazon.com/dp/0123944244"
                      title="Digital Design and Computer Architecture – Harris & Harris"
                      description="Builds strong intuition on how Verilog maps to real hardware systems."
                      accentColor="green"
                    />
                    <BookItem
                      href="https://www.amazon.com/dp/0470185325"
                      title="FPGA Prototyping by Verilog Examples – Pong P. Chu"
                      description="Hands-on Verilog examples focused on practical FPGA design."
                      accentColor="green"
                    />
                  </ul>
                </CardContent>
              </Card>

              {/* SystemVerilog Books */}
              <Card className="border-border shadow-sm hover:shadow-md transition-shadow duration-200">
                <CardHeader>
                  <div className="flex items-center justify-between mb-2">
                    <CardTitle className="text-lg">SystemVerilog</CardTitle>
                    <Badge variant="outline" className="bg-blue-500/10 text-blue-600 border-blue-500/20">
                      Intermediate
                    </Badge>
                  </div>
                  <CardDescription>
                    Advanced resources for SystemVerilog design and verification
                  </CardDescription>
                </CardHeader>
                <CardContent>
                  <ul className="space-y-3 text-sm">
                    <BookItem
                      href="https://www.amazon.com/dp/0387333991"
                      title="SystemVerilog for Design – Stuart Sutherland"
                      description="Authoritative guide to SystemVerilog language features for RTL design."
                      accentColor="blue"
                    />
                    <BookItem
                      href="https://www.amazon.com/dp/038726731X"
                      title="SystemVerilog for Verification – Chris Spear"
                      description="Core reference for verification concepts before moving to UVM."
                      accentColor="blue"
                    />
                    <BookItem
                      href="https://www.amazon.com/dp/1546776346"
                      title="RTL Modeling with SystemVerilog – Stuart Sutherland"
                      description="Best practices for writing clean, synthesizable SystemVerilog RTL."
                      accentColor="blue"
                    />
                  </ul>
                </CardContent>
              </Card>

              {/* UVM Books */}
              <Card className="border-border shadow-sm hover:shadow-md transition-shadow duration-200">
                <CardHeader>
                  <div className="flex items-center justify-between mb-2">
                    <CardTitle className="text-lg">UVM</CardTitle>
                    <Badge variant="outline" className="bg-purple-500/10 text-purple-600 border-purple-500/20">
                      Advanced
                    </Badge>
                  </div>
                  <CardDescription>
                    Comprehensive guides for UVM methodology and best practices
                  </CardDescription>
                </CardHeader>
                <CardContent>
                  <ul className="space-y-3 text-sm">
                    <BookItem
                      href="https://www.amazon.com/dp/0974164938"
                      title="The UVM Primer – Ray Salemi"
                      description="Beginner-friendly introduction to the UVM methodology."
                      accentColor="purple"
                    />
                    <BookItem
                      href="https://verificationacademy.com/cookbook"
                      title="UVM Cookbook – Accellera"
                      description="Official UVM best practices and reference examples."
                      accentColor="purple"
                    />
                    <BookItem
                      href="https://www.doulos.com/books/advanced-uvm/"
                      title="Advanced UVM – Doulos"
                      description="Advanced UVM patterns used in real production environments."
                      accentColor="purple"
                    />
                  </ul>
                </CardContent>
              </Card>
            </div>
          </section>

          {/* Official Standards & Documentation */}
          <section>
            <div className="flex items-center gap-3 mb-6">
              <div className="w-10 h-10 rounded-lg bg-primary/10 flex items-center justify-center">
                <FileText className="w-5 h-5 text-primary" />
              </div>
              <h2 className="text-2xl font-bold">Official Standards & Documentation</h2>
            </div>
            
            <Card className="border-border">
              <CardContent className="pt-6">
                <p className="text-muted-foreground mb-6">
                  Official IEEE standards and language reference manuals are the authoritative sources 
                  for understanding the complete specification of hardware description languages.
                </p>
                <div className="grid md:grid-cols-2 gap-6">
                  {/* IEEE 1364 */}
                  <div className="p-5 bg-muted/30 rounded-xl border border-border/50 hover:border-border hover:shadow-sm transition-all duration-200">
                    <h4 className="font-semibold mb-2 text-foreground">IEEE 1364 – Verilog Standard</h4>
                    <p className="text-sm text-muted-foreground mb-4">
                      Official IEEE language reference manual defining Verilog HDL syntax and semantics.
                    </p>
                    <div className="space-y-2">
                      <a
                        href="https://standards.ieee.org/standard/1364-2005.html"
                        target="_blank"
                        rel="noopener noreferrer"
                        className="group flex items-center gap-2 text-sm text-primary hover:text-primary/80 transition-colors"
                      >
                        <ExternalLink className="w-3.5 h-3.5" />
                        <span className="group-hover:underline">IEEE Standard Page</span>
                      </a>
                      <div className="flex items-center gap-2 text-sm text-muted-foreground/70">
                        <Lock className="w-3.5 h-3.5" />
                        <span>Full PDF available via IEEE (paid or academic access)</span>
                      </div>
                    </div>
                  </div>

                  {/* IEEE 1800 */}
                  <div className="p-5 bg-muted/30 rounded-xl border border-border/50 hover:border-border hover:shadow-sm transition-all duration-200">
                    <h4 className="font-semibold mb-2 text-foreground">IEEE 1800 – SystemVerilog Standard</h4>
                    <p className="text-sm text-muted-foreground mb-4">
                      Official IEEE standard for the unified design and verification language.
                    </p>
                    <div className="space-y-2">
                      <a
                        href="https://standards.ieee.org/standard/1800-2017.html"
                        target="_blank"
                        rel="noopener noreferrer"
                        className="group flex items-center gap-2 text-sm text-primary hover:text-primary/80 transition-colors"
                      >
                        <ExternalLink className="w-3.5 h-3.5" />
                        <span className="group-hover:underline">IEEE Standard Page</span>
                      </a>
                      <a
                        href="https://ieeexplore.ieee.org/document/8299595"
                        target="_blank"
                        rel="noopener noreferrer"
                        className="group flex items-center gap-2 text-sm text-primary hover:text-primary/80 transition-colors"
                      >
                        <ExternalLink className="w-3.5 h-3.5" />
                        <span className="group-hover:underline">IEEE Xplore (academic access)</span>
                      </a>
                      <div className="flex items-center gap-2 text-sm text-muted-foreground/70">
                        <Lock className="w-3.5 h-3.5" />
                        <span>Full PDF requires paid or university access</span>
                      </div>
                    </div>
                  </div>

                  {/* UVM Reference Manual */}
                  <div className="p-5 bg-muted/30 rounded-xl border border-border/50 hover:border-border hover:shadow-sm transition-all duration-200">
                    <h4 className="font-semibold mb-2 text-foreground">UVM Reference Manual</h4>
                    <p className="text-sm text-muted-foreground mb-4">
                      Official documentation for the Universal Verification Methodology class library.
                    </p>
                    <div className="space-y-2">
                      <a
                        href="https://accellera.org/downloads/standards/uvm"
                        target="_blank"
                        rel="noopener noreferrer"
                        className="group flex items-center gap-2 text-sm text-emerald-600 dark:text-emerald-400 hover:text-emerald-500 transition-colors"
                      >
                        <CheckCircle className="w-3.5 h-3.5" />
                        <span className="group-hover:underline">Accellera Downloads (Free)</span>
                      </a>
                      <a
                        href="https://verificationacademy.com/uvm"
                        target="_blank"
                        rel="noopener noreferrer"
                        className="group flex items-center gap-2 text-sm text-emerald-600 dark:text-emerald-400 hover:text-emerald-500 transition-colors"
                      >
                        <CheckCircle className="w-3.5 h-3.5" />
                        <span className="group-hover:underline">Verification Academy Docs (Free)</span>
                      </a>
                    </div>
                  </div>

                  {/* Vendor Documentation */}
                  <div className="p-5 bg-muted/30 rounded-xl border border-border/50 hover:border-border hover:shadow-sm transition-all duration-200">
                    <h4 className="font-semibold mb-2 text-foreground">Vendor Documentation</h4>
                    <p className="text-sm text-muted-foreground mb-4">
                      Official tool documentation, language references, and best practices from EDA vendors.
                    </p>
                    <div className="space-y-2">
                      <a
                        href="https://www.synopsys.com/verification.html"
                        target="_blank"
                        rel="noopener noreferrer"
                        className="group flex items-center gap-2 text-sm text-primary hover:text-primary/80 transition-colors"
                      >
                        <ExternalLink className="w-3.5 h-3.5" />
                        <span className="group-hover:underline">Synopsys Verification Docs</span>
                      </a>
                      <a
                        href="https://www.cadence.com/en_US/home/training/all-courses.html"
                        target="_blank"
                        rel="noopener noreferrer"
                        className="group flex items-center gap-2 text-sm text-primary hover:text-primary/80 transition-colors"
                      >
                        <ExternalLink className="w-3.5 h-3.5" />
                        <span className="group-hover:underline">Cadence Training & Docs</span>
                      </a>
                      <a
                        href="https://eda.sw.siemens.com/en-US/documentation/"
                        target="_blank"
                        rel="noopener noreferrer"
                        className="group flex items-center gap-2 text-sm text-primary hover:text-primary/80 transition-colors"
                      >
                        <ExternalLink className="w-3.5 h-3.5" />
                        <span className="group-hover:underline">Siemens EDA Documentation</span>
                      </a>
                    </div>
                  </div>
                </div>
                <p className="text-xs text-muted-foreground/60 mt-6 text-center">
                  Some IEEE standards require paid or academic access. Free alternatives and official documentation are linked where available.
                </p>
              </CardContent>
            </Card>
          </section>

          {/* Online Learning Platforms */}
          <section>
            <div className="flex items-center gap-3 mb-6">
              <div className="w-10 h-10 rounded-lg bg-primary/10 flex items-center justify-center">
                <GraduationCap className="w-5 h-5 text-primary" />
              </div>
              <h2 className="text-2xl font-bold">Online Learning Platforms</h2>
            </div>
            
            <Card className="border-border">
              <CardContent className="pt-6">
                <p className="text-muted-foreground mb-4">
                  Interactive courses and tutorials from trusted educational platforms to supplement your learning journey.
                </p>
                <div className="grid md:grid-cols-3 gap-4">
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">Platform Placeholder 1</h4>
                    <p className="text-sm text-muted-foreground">Description of learning platform</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">Platform Placeholder 2</h4>
                    <p className="text-sm text-muted-foreground">Description of learning platform</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">Platform Placeholder 3</h4>
                    <p className="text-sm text-muted-foreground">Description of learning platform</p>
                  </div>
                </div>
              </CardContent>
            </Card>
          </section>

          {/* Tools & Simulators */}
          <section>
            <div className="flex items-center gap-3 mb-6">
              <div className="w-10 h-10 rounded-lg bg-primary/10 flex items-center justify-center">
                <Wrench className="w-5 h-5 text-primary" />
              </div>
              <h2 className="text-2xl font-bold">Tools & Simulators</h2>
            </div>
            
            <Card className="border-border">
              <CardContent className="pt-6">
                <p className="text-muted-foreground mb-4">
                  Industry-standard and open-source tools for simulation, synthesis, and verification workflows.
                </p>
                <div className="grid md:grid-cols-2 lg:grid-cols-4 gap-4">
                  <div className="p-4 bg-muted/50 rounded-lg text-center">
                    <h4 className="font-medium mb-1">Simulator 1</h4>
                    <p className="text-xs text-muted-foreground">Free / Commercial</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg text-center">
                    <h4 className="font-medium mb-1">Simulator 2</h4>
                    <p className="text-xs text-muted-foreground">Open Source</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg text-center">
                    <h4 className="font-medium mb-1">Synthesis Tool</h4>
                    <p className="text-xs text-muted-foreground">FPGA Vendor</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg text-center">
                    <h4 className="font-medium mb-1">Waveform Viewer</h4>
                    <p className="text-xs text-muted-foreground">Free</p>
                  </div>
                </div>
              </CardContent>
            </Card>
          </section>

          {/* Community & Forums */}
          <section>
            <div className="flex items-center gap-3 mb-6">
              <div className="w-10 h-10 rounded-lg bg-primary/10 flex items-center justify-center">
                <Users className="w-5 h-5 text-primary" />
              </div>
              <h2 className="text-2xl font-bold">Community & Forums</h2>
            </div>
            
            <Card className="border-border">
              <CardContent className="pt-6">
                <p className="text-muted-foreground mb-4">
                  Connect with other learners and professionals to ask questions, share knowledge, and stay updated.
                </p>
                <div className="grid md:grid-cols-3 gap-4">
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">Forum Placeholder 1</h4>
                    <p className="text-sm text-muted-foreground">Active Q&A community</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">Forum Placeholder 2</h4>
                    <p className="text-sm text-muted-foreground">Discussion boards</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">Forum Placeholder 3</h4>
                    <p className="text-sm text-muted-foreground">Social groups and channels</p>
                  </div>
                </div>
              </CardContent>
            </Card>
          </section>
        </div>
      </div>
    </div>
  );
};

export default References;
