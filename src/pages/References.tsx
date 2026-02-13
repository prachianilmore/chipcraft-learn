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
          <section className="relative">
            {/* Section background band */}
            <div className="absolute inset-0 -mx-4 px-4 bg-gradient-to-b from-muted/30 via-muted/20 to-transparent rounded-3xl -z-10" />
            
            <div className="flex items-center gap-3 mb-4 pt-8">
              <div className="w-12 h-12 rounded-xl bg-primary/10 flex items-center justify-center">
                <FileText className="w-6 h-6 text-primary" />
              </div>
              <div>
                <h2 className="text-2xl font-bold">Official Standards & Documentation</h2>
                <p className="text-sm text-muted-foreground">Authoritative sources for HDL specifications</p>
              </div>
            </div>
            
            <div className="grid md:grid-cols-2 gap-6 pb-8">
              {/* IEEE 1364 - Verilog */}
              <Card className="border-t-4 border-t-blue-500 shadow-lg hover:shadow-xl hover:-translate-y-1 transition-all duration-300 overflow-hidden">
                <CardHeader className="pb-3">
                  <div className="flex items-start justify-between gap-3">
                    <div className="w-12 h-12 rounded-xl bg-blue-500/10 flex items-center justify-center flex-shrink-0">
                      <BookOpen className="w-6 h-6 text-blue-600 dark:text-blue-400" />
                    </div>
                    <Badge variant="outline" className="bg-blue-500/10 text-blue-600 border-blue-500/20 text-xs">
                      IEEE Standard
                    </Badge>
                  </div>
                  <CardTitle className="text-xl mt-3">IEEE 1364 – Verilog Standard</CardTitle>
                  <CardDescription className="text-sm">
                    Official IEEE language reference manual defining Verilog HDL syntax and semantics.
                  </CardDescription>
                </CardHeader>
                <CardContent className="pt-0">
                  <div className="space-y-2 border-t border-border/50 pt-4">
                    <a
                      href="https://standards.ieee.org/standard/1364-2005.html"
                      target="_blank"
                      rel="noopener noreferrer"
                      className="group flex items-center gap-3 p-3 rounded-lg bg-blue-50/50 dark:bg-blue-950/20 hover:bg-blue-100/70 dark:hover:bg-blue-950/40 transition-colors"
                    >
                      <ExternalLink className="w-4 h-4 text-blue-600 dark:text-blue-400" />
                      <span className="text-sm font-medium text-foreground group-hover:text-blue-600 dark:group-hover:text-blue-400 transition-colors">IEEE Standard Page</span>
                    </a>
                    <div className="flex items-center gap-3 p-3 rounded-lg bg-muted/30">
                      <Lock className="w-4 h-4 text-muted-foreground" />
                      <span className="text-sm text-muted-foreground">Full PDF available via IEEE</span>
                      <Badge variant="outline" className="ml-auto text-xs bg-amber-500/10 text-amber-600 border-amber-500/20">
                        Paid / Academic
                      </Badge>
                    </div>
                  </div>
                </CardContent>
              </Card>

              {/* IEEE 1800 - SystemVerilog */}
              <Card className="border-t-4 border-t-blue-500 shadow-lg hover:shadow-xl hover:-translate-y-1 transition-all duration-300 overflow-hidden">
                <CardHeader className="pb-3">
                  <div className="flex items-start justify-between gap-3">
                    <div className="w-12 h-12 rounded-xl bg-blue-500/10 flex items-center justify-center flex-shrink-0">
                      <BookOpen className="w-6 h-6 text-blue-600 dark:text-blue-400" />
                    </div>
                    <Badge variant="outline" className="bg-blue-500/10 text-blue-600 border-blue-500/20 text-xs">
                      IEEE Standard
                    </Badge>
                  </div>
                  <CardTitle className="text-xl mt-3">IEEE 1800 – SystemVerilog Standard</CardTitle>
                  <CardDescription className="text-sm">
                    Official IEEE standard for the unified design and verification language.
                  </CardDescription>
                </CardHeader>
                <CardContent className="pt-0">
                  <div className="space-y-2 border-t border-border/50 pt-4">
                    <a
                      href="https://standards.ieee.org/standard/1800-2017.html"
                      target="_blank"
                      rel="noopener noreferrer"
                      className="group flex items-center gap-3 p-3 rounded-lg bg-blue-50/50 dark:bg-blue-950/20 hover:bg-blue-100/70 dark:hover:bg-blue-950/40 transition-colors"
                    >
                      <ExternalLink className="w-4 h-4 text-blue-600 dark:text-blue-400" />
                      <span className="text-sm font-medium text-foreground group-hover:text-blue-600 dark:group-hover:text-blue-400 transition-colors">IEEE Standard Page</span>
                    </a>
                    <a
                      href="https://ieeexplore.ieee.org/document/8299595"
                      target="_blank"
                      rel="noopener noreferrer"
                      className="group flex items-center gap-3 p-3 rounded-lg bg-blue-50/50 dark:bg-blue-950/20 hover:bg-blue-100/70 dark:hover:bg-blue-950/40 transition-colors"
                    >
                      <ExternalLink className="w-4 h-4 text-blue-600 dark:text-blue-400" />
                      <span className="text-sm font-medium text-foreground group-hover:text-blue-600 dark:group-hover:text-blue-400 transition-colors">IEEE Xplore</span>
                      <Badge variant="outline" className="ml-auto text-xs bg-amber-500/10 text-amber-600 border-amber-500/20">
                        Academic
                      </Badge>
                    </a>
                    <div className="flex items-center gap-3 p-3 rounded-lg bg-muted/30">
                      <Lock className="w-4 h-4 text-muted-foreground" />
                      <span className="text-sm text-muted-foreground">Full PDF requires paid or university access</span>
                    </div>
                  </div>
                </CardContent>
              </Card>

              {/* UVM Reference Manual */}
              <Card className="border-t-4 border-t-emerald-500 shadow-lg hover:shadow-xl hover:-translate-y-1 transition-all duration-300 overflow-hidden">
                <CardHeader className="pb-3">
                  <div className="flex items-start justify-between gap-3">
                    <div className="w-12 h-12 rounded-xl bg-emerald-500/10 flex items-center justify-center flex-shrink-0">
                      <GraduationCap className="w-6 h-6 text-emerald-600 dark:text-emerald-400" />
                    </div>
                    <Badge variant="outline" className="bg-emerald-500/10 text-emerald-600 border-emerald-500/20 text-xs">
                      Free
                    </Badge>
                  </div>
                  <CardTitle className="text-xl mt-3">UVM Reference Manual</CardTitle>
                  <CardDescription className="text-sm">
                    Official documentation for the Universal Verification Methodology class library.
                  </CardDescription>
                </CardHeader>
                <CardContent className="pt-0">
                  <div className="space-y-2 border-t border-border/50 pt-4">
                    <a
                      href="https://accellera.org/downloads/standards/uvm"
                      target="_blank"
                      rel="noopener noreferrer"
                      className="group flex items-center gap-3 p-3 rounded-lg bg-emerald-50/50 dark:bg-emerald-950/20 hover:bg-emerald-100/70 dark:hover:bg-emerald-950/40 transition-colors"
                    >
                      <CheckCircle className="w-4 h-4 text-emerald-600 dark:text-emerald-400" />
                      <span className="text-sm font-medium text-foreground group-hover:text-emerald-600 dark:group-hover:text-emerald-400 transition-colors">Accellera Downloads</span>
                      <Badge variant="outline" className="ml-auto text-xs bg-emerald-500/10 text-emerald-600 border-emerald-500/20">
                        Free
                      </Badge>
                    </a>
                    <a
                      href="https://verificationacademy.com/uvm"
                      target="_blank"
                      rel="noopener noreferrer"
                      className="group flex items-center gap-3 p-3 rounded-lg bg-emerald-50/50 dark:bg-emerald-950/20 hover:bg-emerald-100/70 dark:hover:bg-emerald-950/40 transition-colors"
                    >
                      <CheckCircle className="w-4 h-4 text-emerald-600 dark:text-emerald-400" />
                      <span className="text-sm font-medium text-foreground group-hover:text-emerald-600 dark:group-hover:text-emerald-400 transition-colors">Verification Academy Docs</span>
                      <Badge variant="outline" className="ml-auto text-xs bg-emerald-500/10 text-emerald-600 border-emerald-500/20">
                        Free
                      </Badge>
                    </a>
                  </div>
                </CardContent>
              </Card>

              {/* Vendor Documentation */}
              <Card className="border-t-4 border-t-slate-400 shadow-lg hover:shadow-xl hover:-translate-y-1 transition-all duration-300 overflow-hidden">
                <CardHeader className="pb-3">
                  <div className="flex items-start justify-between gap-3">
                    <div className="w-12 h-12 rounded-xl bg-slate-500/10 flex items-center justify-center flex-shrink-0">
                      <Wrench className="w-6 h-6 text-slate-600 dark:text-slate-400" />
                    </div>
                    <Badge variant="outline" className="bg-slate-500/10 text-slate-600 border-slate-500/20 text-xs">
                      Vendor Tools
                    </Badge>
                  </div>
                  <CardTitle className="text-xl mt-3">Vendor Documentation</CardTitle>
                  <CardDescription className="text-sm">
                    Official tool documentation, language references, and best practices from EDA vendors.
                  </CardDescription>
                </CardHeader>
                <CardContent className="pt-0">
                  <div className="space-y-2 border-t border-border/50 pt-4">
                    <a
                      href="https://www.synopsys.com/verification.html"
                      target="_blank"
                      rel="noopener noreferrer"
                      className="group flex items-center gap-3 p-3 rounded-lg bg-slate-50/50 dark:bg-slate-950/20 hover:bg-slate-100/70 dark:hover:bg-slate-950/40 transition-colors"
                    >
                      <ExternalLink className="w-4 h-4 text-slate-600 dark:text-slate-400" />
                      <span className="text-sm font-medium text-foreground group-hover:text-slate-600 dark:group-hover:text-slate-400 transition-colors">Synopsys Verification Docs</span>
                    </a>
                    <a
                      href="https://www.cadence.com/en_US/home/training/all-courses.html"
                      target="_blank"
                      rel="noopener noreferrer"
                      className="group flex items-center gap-3 p-3 rounded-lg bg-slate-50/50 dark:bg-slate-950/20 hover:bg-slate-100/70 dark:hover:bg-slate-950/40 transition-colors"
                    >
                      <ExternalLink className="w-4 h-4 text-slate-600 dark:text-slate-400" />
                      <span className="text-sm font-medium text-foreground group-hover:text-slate-600 dark:group-hover:text-slate-400 transition-colors">Cadence Training & Docs</span>
                    </a>
                    <a
                      href="https://eda.sw.siemens.com/en-US/documentation/"
                      target="_blank"
                      rel="noopener noreferrer"
                      className="group flex items-center gap-3 p-3 rounded-lg bg-slate-50/50 dark:bg-slate-950/20 hover:bg-slate-100/70 dark:hover:bg-slate-950/40 transition-colors"
                    >
                      <ExternalLink className="w-4 h-4 text-slate-600 dark:text-slate-400" />
                      <span className="text-sm font-medium text-foreground group-hover:text-slate-600 dark:group-hover:text-slate-400 transition-colors">Siemens EDA Documentation</span>
                    </a>
                  </div>
                </CardContent>
              </Card>
            </div>
            
            <p className="text-xs text-muted-foreground/70 text-center pb-4">
              Some IEEE standards require paid or academic access. Free alternatives and official documentation are linked where available.
            </p>
          </section>

          {/* Online Learning Platforms */}
          <section className="relative">
            {/* Section background band */}
            <div className="absolute inset-0 -mx-4 px-4 bg-gradient-to-b from-purple-50/40 via-blue-50/20 to-transparent dark:from-purple-950/20 dark:via-blue-950/10 dark:to-transparent rounded-3xl -z-10" />
            
            <div className="flex items-center gap-3 mb-4 pt-8">
              <div className="w-12 h-12 rounded-xl bg-primary/10 flex items-center justify-center">
                <GraduationCap className="w-7 h-7 text-primary" />
              </div>
              <div>
                <h2 className="text-2xl font-bold">Online Learning Platforms</h2>
                <p className="text-sm text-muted-foreground">Curated knowledge ecosystem for verification and design engineers</p>
              </div>
            </div>
            
            <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-5 pb-8">
              {/* Verification Academy */}
              <a
                href="https://verificationacademy.com"
                target="_blank"
                rel="noopener noreferrer"
                className="group relative bg-card border border-border rounded-xl p-6 shadow-medium hover:shadow-large hover:-translate-y-1 transition-all duration-300 cursor-pointer overflow-hidden"
              >
                <div className="absolute top-0 left-0 right-0 h-1 bg-gradient-to-r from-purple-500 to-purple-400" />
                <div className="flex items-center justify-between mb-3">
                  <div className="w-10 h-10 rounded-lg bg-purple-500/10 flex items-center justify-center">
                    <GraduationCap className="w-5 h-5 text-purple-600 dark:text-purple-400" />
                  </div>
                  <Badge variant="outline" className="text-[10px] bg-emerald-500/10 text-emerald-600 border-emerald-500/20">
                    Free
                  </Badge>
                </div>
                <div className="flex items-center gap-2 mb-1">
                  <h4 className="font-bold text-foreground group-hover:text-purple-600 dark:group-hover:text-purple-400 transition-colors">Verification Academy</h4>
                  <ExternalLink className="w-3.5 h-3.5 text-muted-foreground opacity-0 group-hover:opacity-100 transition-opacity" />
                </div>
                <p className="text-xs text-purple-600/70 dark:text-purple-400/70 font-medium mb-2">Siemens EDA</p>
                <p className="text-sm text-muted-foreground leading-relaxed">Free UVM tutorials, methodology guides, industry webinars, and reference examples. Widely used by professional verification engineers for learning and debugging real SoC environments.</p>
              </a>

              {/* Accellera */}
              <a
                href="https://accellera.org"
                target="_blank"
                rel="noopener noreferrer"
                className="group relative bg-card border border-border rounded-xl p-6 shadow-medium hover:shadow-large hover:-translate-y-1 transition-all duration-300 cursor-pointer overflow-hidden"
              >
                <div className="absolute top-0 left-0 right-0 h-1 bg-gradient-to-r from-blue-500 to-blue-400" />
                <div className="flex items-center justify-between mb-3">
                  <div className="w-10 h-10 rounded-lg bg-blue-500/10 flex items-center justify-center">
                    <FileText className="w-5 h-5 text-blue-600 dark:text-blue-400" />
                  </div>
                  <Badge variant="outline" className="text-[10px] bg-blue-500/10 text-blue-600 border-blue-500/20">
                    Standards Body
                  </Badge>
                </div>
                <div className="flex items-center gap-2 mb-1">
                  <h4 className="font-bold text-foreground group-hover:text-blue-600 dark:group-hover:text-blue-400 transition-colors">Accellera Systems Initiative</h4>
                  <ExternalLink className="w-3.5 h-3.5 text-muted-foreground opacity-0 group-hover:opacity-100 transition-opacity" />
                </div>
                <p className="text-xs text-blue-600/70 dark:text-blue-400/70 font-medium mb-2">Industry Standards</p>
                <p className="text-sm text-muted-foreground leading-relaxed">Official standards organization behind SystemVerilog and UVM. Source of specifications, updates, and methodology evolution used across the semiconductor industry.</p>
              </a>

              {/* NPTEL */}
              <a
                href="https://nptel.ac.in"
                target="_blank"
                rel="noopener noreferrer"
                className="group relative bg-card border border-border rounded-xl p-6 shadow-medium hover:shadow-large hover:-translate-y-1 transition-all duration-300 cursor-pointer overflow-hidden"
              >
                <div className="absolute top-0 left-0 right-0 h-1 bg-gradient-to-r from-emerald-500 to-emerald-400" />
                <div className="flex items-center justify-between mb-3">
                  <div className="w-10 h-10 rounded-lg bg-emerald-500/10 flex items-center justify-center">
                    <BookOpen className="w-5 h-5 text-emerald-600 dark:text-emerald-400" />
                  </div>
                  <Badge variant="outline" className="text-[10px] bg-emerald-500/10 text-emerald-600 border-emerald-500/20">
                    Academic
                  </Badge>
                </div>
                <div className="flex items-center gap-2 mb-1">
                  <h4 className="font-bold text-foreground group-hover:text-emerald-600 dark:group-hover:text-emerald-400 transition-colors">NPTEL – VLSI & HDL Courses</h4>
                  <ExternalLink className="w-3.5 h-3.5 text-muted-foreground opacity-0 group-hover:opacity-100 transition-opacity" />
                </div>
                <p className="text-xs text-emerald-600/70 dark:text-emerald-400/70 font-medium mb-2">University Courses</p>
                <p className="text-sm text-muted-foreground leading-relaxed">University-level structured video courses covering digital design, HDL implementation, CMOS basics, and VLSI system fundamentals.</p>
              </a>

              {/* Doulos */}
              <a
                href="https://www.doulos.com"
                target="_blank"
                rel="noopener noreferrer"
                className="group relative bg-card border border-border rounded-xl p-6 shadow-medium hover:shadow-large hover:-translate-y-1 transition-all duration-300 cursor-pointer overflow-hidden"
              >
                <div className="absolute top-0 left-0 right-0 h-1 bg-gradient-to-r from-amber-500 to-amber-400" />
                <div className="flex items-center justify-between mb-3">
                  <div className="w-10 h-10 rounded-lg bg-amber-500/10 flex items-center justify-center">
                    <Wrench className="w-5 h-5 text-amber-600 dark:text-amber-400" />
                  </div>
                  <Badge variant="outline" className="text-[10px] bg-amber-500/10 text-amber-600 border-amber-500/20">
                    Professional Training
                  </Badge>
                </div>
                <div className="flex items-center gap-2 mb-1">
                  <h4 className="font-bold text-foreground group-hover:text-amber-600 dark:group-hover:text-amber-400 transition-colors">Doulos Training</h4>
                  <ExternalLink className="w-3.5 h-3.5 text-muted-foreground opacity-0 group-hover:opacity-100 transition-opacity" />
                </div>
                <p className="text-xs text-amber-600/70 dark:text-amber-400/70 font-medium mb-2">Industry Training</p>
                <p className="text-sm text-muted-foreground leading-relaxed">Industry-recognized training material focused on SystemVerilog, UVM, and advanced verification methodologies used in production environments.</p>
              </a>

              {/* Coursera */}
              <a
                href="https://www.coursera.org"
                target="_blank"
                rel="noopener noreferrer"
                className="group relative bg-card border border-border rounded-xl p-6 shadow-medium hover:shadow-large hover:-translate-y-1 transition-all duration-300 cursor-pointer overflow-hidden"
              >
                <div className="absolute top-0 left-0 right-0 h-1 bg-gradient-to-r from-cyan-500 to-cyan-400" />
                <div className="flex items-center justify-between mb-3">
                  <div className="w-10 h-10 rounded-lg bg-cyan-500/10 flex items-center justify-center">
                    <GraduationCap className="w-5 h-5 text-cyan-600 dark:text-cyan-400" />
                  </div>
                  <Badge variant="outline" className="text-[10px] bg-cyan-500/10 text-cyan-600 border-cyan-500/20">
                    Academic
                  </Badge>
                </div>
                <div className="flex items-center gap-2 mb-1">
                  <h4 className="font-bold text-foreground group-hover:text-cyan-600 dark:group-hover:text-cyan-400 transition-colors">Coursera – Digital Design Programs</h4>
                  <ExternalLink className="w-3.5 h-3.5 text-muted-foreground opacity-0 group-hover:opacity-100 transition-opacity" />
                </div>
                <p className="text-xs text-cyan-600/70 dark:text-cyan-400/70 font-medium mb-2">Online Courses</p>
                <p className="text-sm text-muted-foreground leading-relaxed">Academic-style digital design and FPGA courses useful for strengthening hardware fundamentals and RTL concepts.</p>
              </a>
            </div>
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
                <div className="space-y-6">
                  {/* Simulators */}
                  <div>
                    <h4 className="text-xs font-semibold uppercase tracking-wider text-muted-foreground mb-3">Simulators</h4>
                    <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-3">
                      <a href="https://eda.sw.siemens.com/en-US/ic/questa/" target="_blank" rel="noopener noreferrer" className="group p-4 bg-muted/50 rounded-lg hover:bg-blue-50/50 dark:hover:bg-blue-950/20 transition-colors cursor-pointer">
                        <div className="flex items-center justify-between mb-1">
                          <h5 className="font-semibold text-sm text-foreground group-hover:text-blue-600 dark:group-hover:text-blue-400 transition-colors">ModelSim / Questa</h5>
                          <Badge variant="outline" className="text-[10px] bg-blue-500/10 text-blue-600 border-blue-500/20">Industry Standard</Badge>
                        </div>
                        <p className="text-xs text-muted-foreground/80">Siemens EDA</p>
                        <p className="text-xs text-muted-foreground mt-1">Industry-standard HDL simulator for design and verification.</p>
                      </a>
                      <a href="https://www.synopsys.com/verification/simulation/vcs.html" target="_blank" rel="noopener noreferrer" className="group p-4 bg-muted/50 rounded-lg hover:bg-blue-50/50 dark:hover:bg-blue-950/20 transition-colors cursor-pointer">
                        <div className="flex items-center justify-between mb-1">
                          <h5 className="font-semibold text-sm text-foreground group-hover:text-blue-600 dark:group-hover:text-blue-400 transition-colors">VCS</h5>
                          <Badge variant="outline" className="text-[10px] bg-blue-500/10 text-blue-600 border-blue-500/20">Industry Standard</Badge>
                        </div>
                        <p className="text-xs text-muted-foreground/80">Synopsys</p>
                        <p className="text-xs text-muted-foreground mt-1">Enterprise-level verification simulator.</p>
                      </a>
                      <a href="https://www.cadence.com/en_US/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-simulator.html" target="_blank" rel="noopener noreferrer" className="group p-4 bg-muted/50 rounded-lg hover:bg-blue-50/50 dark:hover:bg-blue-950/20 transition-colors cursor-pointer">
                        <div className="flex items-center justify-between mb-1">
                          <h5 className="font-semibold text-sm text-foreground group-hover:text-blue-600 dark:group-hover:text-blue-400 transition-colors">Xcelium</h5>
                          <Badge variant="outline" className="text-[10px] bg-blue-500/10 text-blue-600 border-blue-500/20">Industry Standard</Badge>
                        </div>
                        <p className="text-xs text-muted-foreground/80">Cadence</p>
                        <p className="text-xs text-muted-foreground mt-1">High-performance SoC verification simulator.</p>
                      </a>
                      <a href="http://iverilog.icarus.com/" target="_blank" rel="noopener noreferrer" className="group p-4 bg-muted/50 rounded-lg hover:bg-emerald-50/50 dark:hover:bg-emerald-950/20 transition-colors cursor-pointer">
                        <div className="flex items-center justify-between mb-1">
                          <h5 className="font-semibold text-sm text-foreground group-hover:text-emerald-600 dark:group-hover:text-emerald-400 transition-colors">Icarus Verilog</h5>
                          <Badge variant="outline" className="text-[10px] bg-emerald-500/10 text-emerald-600 border-emerald-500/20">Open Source</Badge>
                        </div>
                        <p className="text-xs text-muted-foreground mt-1">Open-source Verilog simulator for learning and prototyping.</p>
                      </a>
                      <a href="https://www.veripool.org/verilator/" target="_blank" rel="noopener noreferrer" className="group p-4 bg-muted/50 rounded-lg hover:bg-emerald-50/50 dark:hover:bg-emerald-950/20 transition-colors cursor-pointer">
                        <div className="flex items-center justify-between mb-1">
                          <h5 className="font-semibold text-sm text-foreground group-hover:text-emerald-600 dark:group-hover:text-emerald-400 transition-colors">Verilator</h5>
                          <Badge variant="outline" className="text-[10px] bg-emerald-500/10 text-emerald-600 border-emerald-500/20">Open Source</Badge>
                        </div>
                        <p className="text-xs text-muted-foreground mt-1">Open-source high-performance Verilog/SystemVerilog simulator.</p>
                      </a>
                    </div>
                  </div>

                  {/* Waveform Viewers */}
                  <div>
                    <h4 className="text-xs font-semibold uppercase tracking-wider text-muted-foreground mb-3">Waveform Viewers</h4>
                    <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-3">
                      <a href="http://gtkwave.sourceforge.net/" target="_blank" rel="noopener noreferrer" className="group p-4 bg-muted/50 rounded-lg hover:bg-emerald-50/50 dark:hover:bg-emerald-950/20 transition-colors cursor-pointer">
                        <div className="flex items-center justify-between mb-1">
                          <h5 className="font-semibold text-sm text-foreground group-hover:text-emerald-600 dark:group-hover:text-emerald-400 transition-colors">GTKWave</h5>
                          <Badge variant="outline" className="text-[10px] bg-emerald-500/10 text-emerald-600 border-emerald-500/20">Open Source</Badge>
                        </div>
                        <p className="text-xs text-muted-foreground mt-1">Free, open-source waveform viewer for VCD and other formats.</p>
                      </a>
                      <a href="https://eda.sw.siemens.com/en-US/ic/questa/" target="_blank" rel="noopener noreferrer" className="group p-4 bg-muted/50 rounded-lg hover:bg-slate-100/50 dark:hover:bg-slate-950/20 transition-colors cursor-pointer">
                        <div className="flex items-center justify-between mb-1">
                          <h5 className="font-semibold text-sm text-foreground group-hover:text-slate-700 dark:group-hover:text-slate-300 transition-colors">Questa Wave</h5>
                          <Badge variant="outline" className="text-[10px] bg-slate-500/10 text-slate-600 border-slate-500/20">Commercial</Badge>
                        </div>
                        <p className="text-xs text-muted-foreground mt-1">Commercial waveform debugger integrated with Questa simulator.</p>
                      </a>
                    </div>
                  </div>

                  {/* Synthesis Tools */}
                  <div>
                    <h4 className="text-xs font-semibold uppercase tracking-wider text-muted-foreground mb-3">Synthesis Tools</h4>
                    <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-3">
                      <a href="https://www.xilinx.com/products/design-tools/vivado.html" target="_blank" rel="noopener noreferrer" className="group p-4 bg-muted/50 rounded-lg hover:bg-blue-50/50 dark:hover:bg-blue-950/20 transition-colors cursor-pointer">
                        <div className="flex items-center justify-between mb-1">
                          <h5 className="font-semibold text-sm text-foreground group-hover:text-blue-600 dark:group-hover:text-blue-400 transition-colors">Vivado</h5>
                          <Badge variant="outline" className="text-[10px] bg-blue-500/10 text-blue-600 border-blue-500/20">Industry Standard</Badge>
                        </div>
                        <p className="text-xs text-muted-foreground/80">Xilinx (AMD)</p>
                        <p className="text-xs text-muted-foreground mt-1">FPGA synthesis, implementation, and programming suite.</p>
                      </a>
                      <a href="https://www.intel.com/content/www/us/en/software/programmable/quartus-prime/overview.html" target="_blank" rel="noopener noreferrer" className="group p-4 bg-muted/50 rounded-lg hover:bg-blue-50/50 dark:hover:bg-blue-950/20 transition-colors cursor-pointer">
                        <div className="flex items-center justify-between mb-1">
                          <h5 className="font-semibold text-sm text-foreground group-hover:text-blue-600 dark:group-hover:text-blue-400 transition-colors">Quartus</h5>
                          <Badge variant="outline" className="text-[10px] bg-blue-500/10 text-blue-600 border-blue-500/20">Industry Standard</Badge>
                        </div>
                        <p className="text-xs text-muted-foreground/80">Intel FPGA</p>
                        <p className="text-xs text-muted-foreground mt-1">FPGA development suite for Intel/Altera devices.</p>
                      </a>
                    </div>
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
