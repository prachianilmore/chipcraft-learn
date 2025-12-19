import { useParams, useNavigate } from "react-router-dom";
import { Button } from "@/components/ui/button";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { Separator } from "@/components/ui/separator";
import { ArrowLeft, Code } from "lucide-react";
import { useEffect } from "react";
import topics from "@/topics.json";

/* ---------------------------------------------
   MODULE ORDER (FOR NEXT BUTTON)
--------------------------------------------- */
const MODULE_ORDER = [
  "verilog-01-basics-syntax",
  "verilog-02-combinational-logic",
  "verilog-03-sequential-logic",
  "verilog-04-testbenches",
];

/* ================================
   SectionCard (Module detail)
================================ */
const SectionCard = ({
  id,
  title,
  content,
  syntax,
  example,
  vectors,
  subSections,
}: {
  id: string;
  title: string;
  content?: string;
  syntax?: string;
  example?: string;
  vectors?: string;
  subSections?: { title: string; code: string }[];
}) => (
  <Card id={id} className="mb-8 scroll-mt-28">
    <CardHeader>
      <CardTitle className="text-2xl">{title}</CardTitle>
    </CardHeader>

    {content && (
      <CardContent>
        <p className="text-muted-foreground whitespace-pre-line">{content}</p>
      </CardContent>
    )}

    {syntax && (
      <CardContent>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono">{syntax}</code>
        </pre>
      </CardContent>
    )}

    {example && (
      <CardContent>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono">{example}</code>
        </pre>
      </CardContent>
    )}

    {vectors && (
      <CardContent>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono">{vectors}</code>
        </pre>
      </CardContent>
    )}

    {subSections?.map((s, i) => (
      <CardContent key={i}>
        <h4 className="font-semibold mb-2">{s.title}</h4>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono">{s.code}</code>
        </pre>
      </CardContent>
    ))}
  </Card>
);

const ModuleDetail = () => {
  const { slug } = useParams();
  const navigate = useNavigate();
  useEffect(() => {
    window.scrollTo({ top: 0, behavior: "smooth" });
  }, [slug]);
  const currentSlug = slug || "verilog-01-basics-syntax";
  const isVerilog = currentSlug.startsWith("verilog");

  /* ======================================================
     SYSTEMVERILOG + UVM 
  ====================================================== */
  const modulesData: Record<string, any> = {
    "systemverilog-01-from-verilog": {
      id: "SV-01",
      title: "SystemVerilog 01 – From Verilog to SystemVerilog",
      description: "Understand the key improvements SystemVerilog brings over traditional Verilog",
      difficulty: "Intermediate",
      topics: ["New Features", "Enhanced Syntax", "Data Types", "Logic Type"],
      concept: `SystemVerilog extends Verilog with powerful features for design, verification, and assertion.`,
      keyIdeas: [
        "**logic** replaces wire and reg",
        "**always_ff / always_comb** clarify intent",
        "**Interfaces** bundle signals",
        "**Classes** enable verification"
      ],
      exampleCode: `module counter(input logic clk, reset, output logic [3:0] count);
always_ff @(posedge clk) begin
  if (reset) count <= 0;
  else count++;
end
endmodule`,
      explanation: `SystemVerilog improves readability while remaining backward compatible.`
    },

    "systemverilog-02-data-types": {
      id: "SV-02",
      title: "SystemVerilog 02 – Data Types, Arrays, typedef",
      description: "Master SystemVerilog's rich type system",
      difficulty: "Intermediate",
      topics: ["logic", "Arrays", "typedef", "struct"],
      concept: `SystemVerilog introduces powerful data types.`,
      keyIdeas: [
        "**logic** for most signals",
        "**bit** for 2-state",
        "**typedef** for reuse",
        "**struct** groups data"
      ],
      exampleCode: `typedef logic [7:0] byte_t;`,
      explanation: `These features improve clarity and reuse.`
    },

    "systemverilog-03-always-blocks": {
      id: "SV-03",
      title: "SystemVerilog 03 – always_comb, always_ff",
      description: "Intent-specific always blocks",
      difficulty: "Intermediate",
      topics: ["always_comb", "always_ff"],
      concept: `Intent-specific always blocks catch bugs early.`,
      keyIdeas: [
        "**always_comb** for combinational",
        "**always_ff** for sequential"
      ],
      exampleCode: `always_comb y = a & b;`,
      explanation: `Tools can validate correct usage.`
    },

    "systemverilog-04-interfaces": {
      id: "SV-04",
      title: "SystemVerilog 04 – Interfaces & Modports",
      description: "Simplify module connections",
      difficulty: "Intermediate",
      topics: ["Interfaces", "Modports"],
      concept: `Interfaces bundle related signals.`,
      keyIdeas: [
        "**Interface** groups signals",
        "**Modport** defines access"
      ],
      exampleCode: `interface bus; logic valid; endinterface`,
      explanation: `Reduces wiring complexity.`
    },

    "systemverilog-05-assertions": {
      id: "SV-05",
      title: "SystemVerilog 05 – Assertions",
      description: "Property-based verification",
      difficulty: "Intermediate",
      topics: ["Assertions"],
      concept: `Assertions continuously check behavior.`,
      keyIdeas: [
        "**Immediate assertions**",
        "**Concurrent assertions**"
      ],
      exampleCode: `assert (a < 10);`,
      explanation: `Catches bugs early in simulation.`
    },

    "uvm-01-why-uvm": {
      id: "UVM-01",
      title: "UVM 01 – Why UVM?",
      description: "Motivation for UVM",
      difficulty: "Advanced",
      topics: ["Verification Crisis", "Reusability"],
      concept: `UVM addresses verification scalability.`,
      keyIdeas: [
        "**Reusable components**",
        "**Constrained random testing**"
      ],
      exampleCode: `class transaction extends uvm_sequence_item; endclass`,
      explanation: `Industry-standard verification methodology.`
    },

    "uvm-02-architecture": {
      id: "UVM-02",
      title: "UVM 02 – Testbench Architecture",
      description: "Layered UVM testbench",
      difficulty: "Advanced",
      topics: ["Test", "Env", "Agent"],
      concept: `UVM testbench hierarchy.`,
      keyIdeas: [
        "**Test** controls flow",
        "**Agent** groups components"
      ],
      exampleCode: `class my_env extends uvm_env; endclass`,
      explanation: `Enables reuse and scalability.`
    },

    "uvm-03-transactions-sequences": {
      id: "UVM-03",
      title: "UVM 03 – Transactions & Sequences",
      description: "Stimulus generation",
      difficulty: "Advanced",
      topics: ["Sequence", "Driver"],
      concept: `Stimulus flows via sequences.`,
      keyIdeas: [
        "**Sequence items**",
        "**Sequencer**"
      ],
      exampleCode: `start_item(tr); finish_item(tr);`,
      explanation: `Separates WHAT vs HOW.`
    },

    "uvm-04-monitors-scoreboards": {
      id: "UVM-04",
      title: "UVM 04 – Monitors & Scoreboards",
      description: "Checking DUT behavior",
      difficulty: "Advanced",
      topics: ["Monitor", "Scoreboard"],
      concept: `Passive checking.`,
      keyIdeas: [
        "**Monitor** observes",
        "**Scoreboard** checks"
      ],
      exampleCode: `ap.write(tr);`,
      explanation: `Automatic verification.`
    },

    "uvm-05-mini-example": {
      id: "UVM-05",
      title: "UVM 05 – Mini UVM Example",
      description: "End-to-end UVM flow",
      difficulty: "Advanced",
      topics: ["Complete Flow"],
      concept: `All components working together.`,
      keyIdeas: [
        "**Build phase**",
        "**Run phase**"
      ],
      exampleCode: `run_test("mini_test");`,
      explanation: `Shows full UVM flow.`
    }
  };

  const module = isVerilog
    ? topics[currentSlug as keyof typeof topics]
    : modulesData[currentSlug];

  if (!module) {
    return (
      <div className="min-h-screen py-20 text-center">
        <h1 className="text-3xl font-bold mb-4">Module Not Found</h1>
        <Button onClick={() => navigate("/verilog-modules")}>
          <ArrowLeft className="mr-2" /> Back
        </Button>
      </div>
    );
  }

  const currentIndex = MODULE_ORDER.indexOf(currentSlug);
  const nextModule =
    currentIndex !== -1 && currentIndex < MODULE_ORDER.length - 1
      ? MODULE_ORDER[currentIndex + 1]
      : null;

  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4 max-w-4xl">
        <Button variant="ghost" onClick={() => navigate("/verilog-modules")} className="mb-6">
          <ArrowLeft className="mr-2" /> Back
        </Button>

        <div className="mb-8">
          <div className="flex items-center gap-3 mb-4">
            <div className="w-12 h-12 rounded-lg bg-primary/10 flex items-center justify-center">
              <Code className="w-6 h-6 text-primary" />
            </div>
            <Badge variant="outline">{module.difficulty}</Badge>
          </div>

          <div className="text-sm font-mono text-muted-foreground mb-2">
            Module {module.id}
          </div>

          <h1 className="text-4xl font-bold mb-4">{module.title}</h1>
          <p className="text-muted-foreground">{module.description}</p>

          {isVerilog && (
            <div className="flex flex-wrap gap-3 mt-6">
              {module.sections.map((s: any, i: number) => (
                <a
                  key={i}
                  href={`#section-${i}`}
                  className="px-4 py-1.5 rounded-full text-sm font-medium
                             bg-blue-50 text-blue-700 hover:bg-blue-100 transition"
                >
                  {s.title.replace(/^\d+\.\s*/, "")}
                </a>
              ))}
            </div>
          )}
        </div>

        <Separator className="my-8" />

        {isVerilog ? (
          module.sections.map((s: any, i: number) => (
            <SectionCard
              key={i}
              id={`section-${i}`}
              title={s.title}
              content={s.content}
              syntax={s.syntax}
              example={s.example}
              vectors={s.vectors}
              subSections={s.subSections}
            />
          ))
        ) : (
          <>
            {module.concept && (
              <Card className="mb-6">
                <CardHeader><CardTitle>Concept</CardTitle></CardHeader>
                <CardContent>{module.concept}</CardContent>
              </Card>
            )}
            {module.keyIdeas && (
              <Card className="mb-6">
                <CardHeader><CardTitle>Key Ideas</CardTitle></CardHeader>
                <CardContent>
                  <ul>
                    {module.keyIdeas.map((k: string, i: number) => (
                      <li key={i} dangerouslySetInnerHTML={{ __html: k }} />
                    ))}
                  </ul>
                </CardContent>
              </Card>
            )}
            {module.exampleCode && (
              <Card className="mb-6">
                <CardHeader><CardTitle>Example Code</CardTitle></CardHeader>
                <CardContent>
                  <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
                    <code>{module.exampleCode}</code>
                  </pre>
                </CardContent>
              </Card>
            )}
            {module.explanation && (
              <Card className="mb-6">
                <CardHeader><CardTitle>Explanation</CardTitle></CardHeader>
                <CardContent>{module.explanation}</CardContent>
              </Card>
            )}
          </>
        )}

        <div className="mt-12 flex justify-between items-center">
          <Button variant="outline" onClick={() => navigate("/verilog-modules")}>
            <ArrowLeft className="mr-2" /> All Modules
          </Button>

          {nextModule && (
            <Button onClick={() => navigate(`/modules/${nextModule}`)}>
              Next Module →
            </Button>
          )}
        </div>
      </div>
    </div>
  );
};

export default ModuleDetail;
