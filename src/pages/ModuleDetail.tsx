import { useParams, useNavigate } from "react-router-dom";
import { useEffect } from "react";
import { Button } from "@/components/ui/button";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { Separator } from "@/components/ui/separator";
import { ArrowLeft, Code } from "lucide-react";
import topics from "@/topics.json";

/* ---------------------------------------------
   MODULE ORDER (SEPARATE TRACKS)
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
  "uvm-02-testbench-architecture",
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
    <p
      className="text-muted-foreground leading-relaxed"
      dangerouslySetInnerHTML={{ __html: content }}
    />
  </CardContent>
)}

    {syntax && (
      <CardContent>
        <h4 className="font-semibold mb-2">Syntax</h4>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono whitespace-pre">{syntax}</code>
        </pre>
      </CardContent>
    )}

    {example && (
      <CardContent>
        <h4 className="font-semibold mb-2">Example</h4>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono whitespace-pre">{example}</code>
        </pre>
      </CardContent>
    )}

    {vectors && (
      <CardContent>
        <h4 className="font-semibold mb-2">Vectors</h4>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono whitespace-pre">{vectors}</code>
        </pre>
      </CardContent>
    )}

    {subSections?.map((s, i) => (
      <CardContent key={i}>
        <h4 className="font-semibold mb-2">{s.title}</h4>
        <pre className="bg-muted/50 p-4 rounded-lg overflow-x-auto">
          <code className="font-mono whitespace-pre">{s.code}</code>
        </pre>
      </CardContent>
    ))}
  </Card>
);

/* ---------------------------------------------
   Module Detail
--------------------------------------------- */
const ModuleDetail = () => {
  const { slug } = useParams();
  const navigate = useNavigate();

  const currentSlug: string = slug ?? "";

  useEffect(() => {
    window.scrollTo({ top: 0, behavior: "smooth" });
  }, [slug]);

  const module = topics[currentSlug as keyof typeof topics];

  const isSystemVerilog = currentSlug.startsWith("systemverilog");
  const isUVM = currentSlug.startsWith("uvm");

  const moduleOrder = isUVM
    ? UVM_MODULE_ORDER
    : isSystemVerilog
    ? SYSTEMVERILOG_MODULE_ORDER
    : VERILOG_MODULE_ORDER;

  const currentIndex = moduleOrder.indexOf(currentSlug);

  const nextSlug =
    currentIndex !== -1 && currentIndex < moduleOrder.length - 1
      ? moduleOrder[currentIndex + 1]
      : null;

  if (!module) {
    return (
      <div className="min-h-screen flex flex-col items-center justify-center gap-4">
        <h2 className="text-xl font-semibold">Module not found</h2>
        <Button onClick={() => navigate("/modules")}>Go Back</Button>
      </div>
    );
  }

  return (
    <div className="min-h-screen py-20">
      <div className="container mx-auto px-4 max-w-4xl">

        {/* Back Button */}
        <Button
          variant="ghost"
          onClick={() => {
            if (
              currentSlug === VERILOG_MODULE_ORDER[0] ||
              currentSlug === SYSTEMVERILOG_MODULE_ORDER[0] ||
              currentSlug === UVM_MODULE_ORDER[0]
            ) {
              navigate("/modules");
            } else {
              navigate(`/modules/${moduleOrder[currentIndex - 1]}`);
            }

            setTimeout(() => {
              window.scrollTo({ top: 0, behavior: "smooth" });
            }, 0);
          }}
        >
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
            vectors={s.vectors}
            subSections={s.subSections}
          />
        ))}

        {/* Bottom Navigation */}
        <div className="mt-12 flex justify-between items-center">
          <Button variant="outline" onClick={() => navigate("/modules")}>
            <ArrowLeft className="mr-2" /> All Modules
          </Button>

          {nextSlug && (
            <Button onClick={() => navigate(`/modules/${nextSlug}`)}>
              Next Module
              <ArrowLeft className="rotate-180 ml-2" />
            </Button>
          )}
        </div>
      </div>
    </div>
  );
};

export default ModuleDetail;
