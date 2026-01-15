import { useParams, useNavigate } from "react-router-dom";
import { useEffect } from "react";
import { Button } from "@/components/ui/button";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { Separator } from "@/components/ui/separator";
import { ArrowLeft, Code } from "lucide-react";
import topics from "@/topics.json";

/* ---------------------------------------------
   MODULE ORDER (TRACKS)
--------------------------------------------- */
const VERILOG_MODULE_ORDER = [
  "verilog-01-basics-syntax",
  "verilog-02-combinational-logic",
  "verilog-03-sequential-logic",
  "verilog-04-testbenches",
];

const SYSTEMVERILOG_MODULE_ORDER = [
  "systemverilog-01-from-verilog",
  "systemverilog-02-data-types",
  "systemverilog-03-always-blocks",
  "systemverilog-04-interfaces",
  "systemverilog-05-assertions",
];

const UVM_MODULE_ORDER = [
  "uvm-01-why-uvm",
  "uvm-02-architecture",
  "uvm-03-transactions-sequences",
  "uvm-04-monitors-scoreboards",
  "uvm-05-mini-environment",
];

/* ---------------------------------------------
   SectionCard
--------------------------------------------- */
const SectionCard = ({
  id,
  title,
  content,
  syntax,
  example,
}: {
  id: string;
  title: string;
  content?: string;
  syntax?: string;
  example?: string;
}) => (
  <Card id={id} className="mb-8 scroll-mt-28">
    <CardHeader>
      <CardTitle className="text-2xl">{title}</CardTitle>
    </CardHeader>

    {content && (
      <CardContent>
        <div
          className="text-muted-foreground leading-relaxed space-y-2"
          dangerouslySetInnerHTML={{ __html: content }}
        />
      </CardContent>
    )}

    {syntax && (
      <CardContent>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono whitespace-pre">{syntax}</code>
        </pre>
      </CardContent>
    )}

    {example && (
      <CardContent>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono whitespace-pre">{example}</code>
        </pre>
      </CardContent>
    )}
  </Card>
);

/* ---------------------------------------------
   Module Detail
--------------------------------------------- */
const ModuleDetail = () => {
  const { slug } = useParams();
  const navigate = useNavigate();
  const currentSlug = slug ?? "";

  useEffect(() => {
    window.scrollTo({ top: 0 });
  }, [currentSlug]);

  const module = topics[currentSlug as keyof typeof topics];

  if (!module) {
    return (
      <div className="min-h-screen flex flex-col items-center justify-center gap-4">
        <h2 className="text-xl font-semibold">Module not found</h2>
        <Button onClick={() => navigate("/modules")}>Go Back</Button>
      </div>
    );
  }

  /* ---------------------------------------------
     Track detection
  --------------------------------------------- */
  let moduleOrder: string[] = [];
  let trackRoot = "/modules";

  if (currentSlug.startsWith("verilog")) {
    moduleOrder = VERILOG_MODULE_ORDER;
    trackRoot = "/verilog-modules";
  } else if (currentSlug.startsWith("systemverilog")) {
    moduleOrder = SYSTEMVERILOG_MODULE_ORDER;
    trackRoot = "/systemverilog-modules";
  } else if (currentSlug.startsWith("uvm")) {
    moduleOrder = UVM_MODULE_ORDER;
    trackRoot = "/uvm-modules";
  }

  const currentIndex = moduleOrder.indexOf(currentSlug);

  /* ---------------------------------------------
     Back button logic
  --------------------------------------------- */
  const handleBack = () => {
    if (currentIndex <= 0) {
      navigate(trackRoot);
    } else {
      navigate(`/modules/${moduleOrder[currentIndex - 1]}`);
    }

    requestAnimationFrame(() => {
      window.scrollTo({ top: 0, behavior: "smooth" });
    });
  };

  /* ---------------------------------------------
     Next module logic
  --------------------------------------------- */
  const nextSlug =
    currentIndex !== -1 && currentIndex < moduleOrder.length - 1
      ? moduleOrder[currentIndex + 1]
      : null;

  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4 max-w-4xl">

        {/* Back Button */}
        <Button variant="ghost" onClick={handleBack}>
          <ArrowLeft className="mr-2" /> Back
        </Button>

        {/* Header */}
        <div className="my-8">
          <div className="flex items-center gap-3 mb-4">
            <div className="w-12 h-12 rounded-lg bg-primary/10 flex items-center justify-center">
              <Code className="w-6 h-6 text-primary" />
            </div>
            <Badge variant="outline">{module.difficulty}</Badge>
          </div>

          <div className="text-sm font-mono text-muted-foreground">
            Module {module.id}
          </div>

          <h1 className="text-4xl font-bold mb-4">{module.title}</h1>
          <p className="text-muted-foreground">{module.description}</p>

          <div className="flex flex-wrap gap-3 mt-6">
            {module.sections.map((section: any, index: number) => (
              <a
                key={index}
                href={`#section-${index}`}
                className="px-4 py-1.5 rounded-full text-sm font-medium
                           bg-blue-50 text-blue-700 hover:bg-blue-100 transition"
              >
                {section.title.replace(/^\d+\.\s*/, "")}
              </a>
            ))}
          </div>
        </div>

        <Separator className="my-8" />

        {/* Sections */}
        {module.sections.map((s: any, i: number) => (
          <SectionCard
            key={i}
            id={`section-${i}`}
            title={s.title}
            content={s.content}
            syntax={s.syntax}
            example={s.example}
          />
        ))}

        {/* Bottom Navigation */}
        <div className="mt-12 flex justify-between items-center">
          <Button variant="outline" onClick={() => navigate("/modules")}>
            <ArrowLeft className="mr-2" /> All Modules
          </Button>

          {nextSlug && (
            <Button
              onClick={() => {
                navigate(`/modules/${nextSlug}`);
                requestAnimationFrame(() => {
                  window.scrollTo({ top: 0, behavior: "smooth" });
                });
              }}
              className="flex items-center gap-2"
            >
              Next Module
              <ArrowLeft className="rotate-180" />
            </Button>
          )}
        </div>
      </div>
    </div>
  );
};

export default ModuleDetail;
