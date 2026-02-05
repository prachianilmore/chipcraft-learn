import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { BookOpen, FileText, GraduationCap, Wrench, Users } from "lucide-react";

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
              <Card className="border-border">
                <CardHeader>
                  <div className="flex items-center justify-between mb-2">
                    <CardTitle className="text-lg">Verilog</CardTitle>
                    <Badge variant="outline" className="bg-green-500/10 text-green-600 border-green-500/20">
                      Beginner
                    </Badge>
                  </div>
                  <CardDescription>
                    Essential books for learning Verilog HDL fundamentals
                  </CardDescription>
                </CardHeader>
                <CardContent>
                  <ul className="space-y-3 text-sm">
                    <li className="p-3 bg-muted/50 rounded-md">
                      <a href="https://www.amazon.com/dp/0130449113" target="_blank" rel="noopener noreferrer" className="font-medium text-foreground hover:text-primary transition-colors">
                        Verilog HDL: A Guide to Digital Design and Synthesis – Samir Palnitkar
                      </a>
                      <p className="text-muted-foreground mt-1">Industry-standard introduction to Verilog HDL and synthesizable design concepts.</p>
                    </li>
                    <li className="p-3 bg-muted/50 rounded-md">
                      <a href="https://www.amazon.com/dp/0123944244" target="_blank" rel="noopener noreferrer" className="font-medium text-foreground hover:text-primary transition-colors">
                        Digital Design and Computer Architecture – Harris & Harris
                      </a>
                      <p className="text-muted-foreground mt-1">Builds strong intuition on how Verilog maps to real hardware systems.</p>
                    </li>
                    <li className="p-3 bg-muted/50 rounded-md">
                      <a href="https://www.amazon.com/dp/0470185325" target="_blank" rel="noopener noreferrer" className="font-medium text-foreground hover:text-primary transition-colors">
                        FPGA Prototyping by Verilog Examples – Pong P. Chu
                      </a>
                      <p className="text-muted-foreground mt-1">Hands-on Verilog examples focused on practical FPGA design.</p>
                    </li>
                  </ul>
                </CardContent>
              </Card>

              {/* SystemVerilog Books */}
              <Card className="border-border">
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
                    <li className="p-3 bg-muted/50 rounded-md">
                      <a href="https://www.amazon.com/dp/0387333991" target="_blank" rel="noopener noreferrer" className="font-medium text-foreground hover:text-primary transition-colors">
                        SystemVerilog for Design – Stuart Sutherland
                      </a>
                      <p className="text-muted-foreground mt-1">Authoritative guide to SystemVerilog language features for RTL design.</p>
                    </li>
                    <li className="p-3 bg-muted/50 rounded-md">
                      <a href="https://www.amazon.com/dp/038726731X" target="_blank" rel="noopener noreferrer" className="font-medium text-foreground hover:text-primary transition-colors">
                        SystemVerilog for Verification – Chris Spear
                      </a>
                      <p className="text-muted-foreground mt-1">Core reference for verification concepts before moving to UVM.</p>
                    </li>
                    <li className="p-3 bg-muted/50 rounded-md">
                      <a href="https://www.amazon.com/dp/1546776346" target="_blank" rel="noopener noreferrer" className="font-medium text-foreground hover:text-primary transition-colors">
                        RTL Modeling with SystemVerilog – Stuart Sutherland
                      </a>
                      <p className="text-muted-foreground mt-1">Best practices for writing clean, synthesizable SystemVerilog RTL.</p>
                    </li>
                  </ul>
                </CardContent>
              </Card>

              {/* UVM Books */}
              <Card className="border-border">
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
                    <li className="p-3 bg-muted/50 rounded-md">
                      <a href="https://www.amazon.com/dp/0974164938" target="_blank" rel="noopener noreferrer" className="font-medium text-foreground hover:text-primary transition-colors">
                        The UVM Primer – Ray Salemi
                      </a>
                      <p className="text-muted-foreground mt-1">Beginner-friendly introduction to the UVM methodology.</p>
                    </li>
                    <li className="p-3 bg-muted/50 rounded-md">
                      <a href="https://verificationacademy.com/cookbook" target="_blank" rel="noopener noreferrer" className="font-medium text-foreground hover:text-primary transition-colors">
                        UVM Cookbook – Accellera
                      </a>
                      <p className="text-muted-foreground mt-1">Official UVM best practices and reference examples.</p>
                    </li>
                    <li className="p-3 bg-muted/50 rounded-md">
                      <a href="https://www.doulos.com/books/advanced-uvm/" target="_blank" rel="noopener noreferrer" className="font-medium text-foreground hover:text-primary transition-colors">
                        Advanced UVM – Doulos
                      </a>
                      <p className="text-muted-foreground mt-1">Advanced UVM patterns used in real production environments.</p>
                    </li>
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
                <p className="text-muted-foreground mb-4">
                  Official IEEE standards and language reference manuals are the authoritative sources 
                  for understanding the complete specification of hardware description languages.
                </p>
                <div className="grid md:grid-cols-2 gap-4">
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">IEEE 1364 - Verilog Standard</h4>
                    <p className="text-sm text-muted-foreground">Official Verilog HDL specification</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">IEEE 1800 - SystemVerilog Standard</h4>
                    <p className="text-sm text-muted-foreground">Unified hardware design and verification language</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">UVM Reference Manual</h4>
                    <p className="text-sm text-muted-foreground">Official UVM class library documentation</p>
                  </div>
                  <div className="p-4 bg-muted/50 rounded-lg">
                    <h4 className="font-medium mb-1">Vendor Documentation</h4>
                    <p className="text-sm text-muted-foreground">Tool-specific guides and tutorials</p>
                  </div>
                </div>
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
