import { useState, useMemo } from "react";
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Button } from "@/components/ui/button";
import { Badge } from "@/components/ui/badge";
import { Progress } from "@/components/ui/progress";
import { Switch } from "@/components/ui/switch";
import { Label } from "@/components/ui/label";
import { Textarea } from "@/components/ui/textarea";
import { Select, SelectContent, SelectItem, SelectTrigger, SelectValue } from "@/components/ui/select";
import { CheckCircle2, XCircle, Flag, RotateCcw, Play, ChevronLeft, ChevronRight, Send } from "lucide-react";
import { quizQuestions, QuizQuestion, Topic, Difficulty } from "@/data/quizQuestions";

type QuizState = "setup" | "inProgress" | "review";

interface UserAnswer {
  questionId: number;
  answer: string;
  flagged: boolean;
  selfChecked?: boolean;
}

const Quiz = () => {
  const [quizState, setQuizState] = useState<QuizState>("setup");
  const [currentIndex, setCurrentIndex] = useState(0);
  const [userAnswers, setUserAnswers] = useState<Map<number, UserAnswer>>(new Map());
  const [practiceMode, setPracticeMode] = useState(false);
  const [topicFilter, setTopicFilter] = useState<string>("All");
  const [difficultyFilter, setDifficultyFilter] = useState<string>("All");
  const [showPracticeExplanation, setShowPracticeExplanation] = useState(false);

  const filteredQuestions = useMemo(() => {
    return quizQuestions.filter(q => {
      const topicMatch = topicFilter === "All" || q.topic === topicFilter;
      const diffMatch = difficultyFilter === "All" || q.difficulty === difficultyFilter;
      return topicMatch && diffMatch;
    });
  }, [topicFilter, difficultyFilter]);

  const currentQuestion = filteredQuestions[currentIndex];

  const handleStartQuiz = () => {
    setQuizState("inProgress");
    setCurrentIndex(0);
    setUserAnswers(new Map());
    setShowPracticeExplanation(false);
  };

  const handleAnswerChange = (questionId: number, answer: string) => {
    const existing = userAnswers.get(questionId);
    setUserAnswers(new Map(userAnswers.set(questionId, {
      questionId,
      answer,
      flagged: existing?.flagged || false,
      selfChecked: existing?.selfChecked
    })));
    if (practiceMode && currentQuestion?.type === "mcq") {
      setShowPracticeExplanation(true);
    }
  };

  const handleFlagToggle = (questionId: number) => {
    const existing = userAnswers.get(questionId);
    setUserAnswers(new Map(userAnswers.set(questionId, {
      questionId,
      answer: existing?.answer || "",
      flagged: !existing?.flagged,
      selfChecked: existing?.selfChecked
    })));
  };

  const handleSelfCheck = (questionId: number, checked: boolean) => {
    const existing = userAnswers.get(questionId);
    if (existing) {
      setUserAnswers(new Map(userAnswers.set(questionId, {
        ...existing,
        selfChecked: checked
      })));
    }
  };

  const handleNext = () => {
    if (currentIndex < filteredQuestions.length - 1) {
      setCurrentIndex(currentIndex + 1);
      setShowPracticeExplanation(false);
    }
  };

  const handlePrevious = () => {
    if (currentIndex > 0) {
      setCurrentIndex(currentIndex - 1);
      setShowPracticeExplanation(false);
    }
  };

  const handleSubmit = () => {
    setQuizState("review");
    setCurrentIndex(0);
  };

  const handleRetry = () => {
    setQuizState("setup");
    setCurrentIndex(0);
    setUserAnswers(new Map());
    setShowPracticeExplanation(false);
  };

  const calculateScore = () => {
    let correct = 0;
    let total = 0;
    filteredQuestions.forEach(q => {
      const userAnswer = userAnswers.get(q.id);
      if (q.type === "mcq") {
        total++;
        if (userAnswer?.answer === q.correctAnswer) correct++;
      } else {
        total++;
        if (userAnswer?.selfChecked) correct++;
      }
    });
    return { correct, total, percentage: total > 0 ? Math.round((correct / total) * 100) : 0 };
  };

  const getBreakdown = () => {
    const breakdown: Record<string, { correct: number; total: number }> = {};
    filteredQuestions.forEach(q => {
      const key = `${q.topic} (${q.difficulty})`;
      if (!breakdown[key]) breakdown[key] = { correct: 0, total: 0 };
      breakdown[key].total++;
      const userAnswer = userAnswers.get(q.id);
      if (q.type === "mcq" && userAnswer?.answer === q.correctAnswer) {
        breakdown[key].correct++;
      } else if (q.type === "coding" && userAnswer?.selfChecked) {
        breakdown[key].correct++;
      }
    });
    return breakdown;
  };

  const getDifficultyColor = (difficulty: Difficulty) => {
    switch (difficulty) {
      case "Easy": return "bg-green-500/20 text-green-400 border-green-500/30";
      case "Medium": return "bg-yellow-500/20 text-yellow-400 border-yellow-500/30";
      case "Hard": return "bg-red-500/20 text-red-400 border-red-500/30";
    }
  };

  const topics: string[] = ["All", "Verilog", "SystemVerilog", "UVM", "Assertions", "Coverage", "Debug", "Coding"];
  const difficulties: string[] = ["All", "Easy", "Medium", "Hard"];

  // Setup Screen
  if (quizState === "setup") {
    return (
      <div className="container mx-auto px-4 py-8 max-w-4xl">
        <div className="text-center mb-8">
          <h1 className="text-4xl font-bold text-foreground mb-4">ChipLearn Quiz (20 Questions)</h1>
          <p className="text-xl text-muted-foreground">Mix of coding + DV interview questions with explanations</p>
        </div>

        <Card className="mb-6">
          <CardHeader>
            <CardTitle>Quiz Settings</CardTitle>
          </CardHeader>
          <CardContent className="space-y-6">
            <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
              <div className="space-y-2">
                <Label>Filter by Topic</Label>
                <Select value={topicFilter} onValueChange={setTopicFilter}>
                  <SelectTrigger><SelectValue /></SelectTrigger>
                  <SelectContent>
                    {topics.map(t => <SelectItem key={t} value={t}>{t}</SelectItem>)}
                  </SelectContent>
                </Select>
              </div>
              <div className="space-y-2">
                <Label>Filter by Difficulty</Label>
                <Select value={difficultyFilter} onValueChange={setDifficultyFilter}>
                  <SelectTrigger><SelectValue /></SelectTrigger>
                  <SelectContent>
                    {difficulties.map(d => <SelectItem key={d} value={d}>{d}</SelectItem>)}
                  </SelectContent>
                </Select>
              </div>
            </div>

            <div className="flex items-center justify-between p-4 bg-muted/50 rounded-lg">
              <div>
                <Label className="text-base font-medium">Practice Mode</Label>
                <p className="text-sm text-muted-foreground">Show explanations immediately after answering</p>
              </div>
              <Switch checked={practiceMode} onCheckedChange={setPracticeMode} />
            </div>

            <div className="text-center p-4 bg-primary/10 rounded-lg">
              <p className="text-lg font-medium">{filteredQuestions.length} questions selected</p>
              <p className="text-sm text-muted-foreground">
                {filteredQuestions.filter(q => q.type === "mcq").length} MCQ • {filteredQuestions.filter(q => q.type === "coding").length} Coding (Self-Check)
              </p>
            </div>

            <Button onClick={handleStartQuiz} size="lg" className="w-full" disabled={filteredQuestions.length === 0}>
              <Play className="w-5 h-5 mr-2" /> Start Quiz
            </Button>
          </CardContent>
        </Card>
      </div>
    );
  }

  // In Progress Screen
  if (quizState === "inProgress" && currentQuestion) {
    const userAnswer = userAnswers.get(currentQuestion.id);
    const isAnswered = !!userAnswer?.answer;
    const showExplanation = practiceMode && showPracticeExplanation && currentQuestion.type === "mcq";
    const isCorrectInPractice = userAnswer?.answer === currentQuestion.correctAnswer;

    return (
      <div className="container mx-auto px-4 py-8 max-w-4xl">
        <div className="mb-6">
          <div className="flex items-center justify-between mb-2">
            <span className="text-sm text-muted-foreground">Question {currentIndex + 1} of {filteredQuestions.length}</span>
            <div className="flex gap-2">
              <Badge className={getDifficultyColor(currentQuestion.difficulty)}>{currentQuestion.difficulty}</Badge>
              <Badge variant="outline">{currentQuestion.topic}</Badge>
              {currentQuestion.type === "coding" && <Badge variant="secondary">Self-Check</Badge>}
            </div>
          </div>
          <Progress value={((currentIndex + 1) / filteredQuestions.length) * 100} className="h-2" />
        </div>

        <Card className="mb-6">
          <CardContent className="pt-6">
            <p className="text-lg font-medium mb-6">{currentQuestion.question}</p>

            {currentQuestion.type === "mcq" && currentQuestion.options && (
              <div className="space-y-3">
                {currentQuestion.options.map((option, idx) => {
                  const letter = String.fromCharCode(65 + idx);
                  const isSelected = userAnswer?.answer === letter;
                  const isCorrect = letter === currentQuestion.correctAnswer;
                  
                  let optionClass = "p-4 border rounded-lg cursor-pointer transition-all ";
                  if (showExplanation) {
                    if (isCorrect) optionClass += "bg-green-500/20 border-green-500";
                    else if (isSelected && !isCorrect) optionClass += "bg-red-500/20 border-red-500";
                    else optionClass += "border-border opacity-50";
                  } else {
                    optionClass += isSelected ? "bg-primary/20 border-primary" : "border-border hover:border-primary/50";
                  }

                  return (
                    <div
                      key={idx}
                      onClick={() => !showExplanation && handleAnswerChange(currentQuestion.id, letter)}
                      className={optionClass}
                    >
                      <span className="font-medium mr-2">{letter}.</span> {option}
                    </div>
                  );
                })}
              </div>
            )}

            {currentQuestion.type === "coding" && (
              <div className="space-y-4">
                {currentQuestion.codePrompt && (
                  <pre className="p-4 bg-muted rounded-lg text-sm overflow-x-auto font-mono">{currentQuestion.codePrompt}</pre>
                )}
                <Textarea
                  placeholder="Write your code/answer here..."
                  value={userAnswer?.answer || ""}
                  onChange={(e) => handleAnswerChange(currentQuestion.id, e.target.value)}
                  className="font-mono min-h-[200px]"
                />
              </div>
            )}

            {showExplanation && (
              <div className={`mt-6 p-4 rounded-lg ${isCorrectInPractice ? "bg-green-500/10 border border-green-500/30" : "bg-red-500/10 border border-red-500/30"}`}>
                <p className="font-medium mb-2 flex items-center gap-2">
                  {isCorrectInPractice ? <CheckCircle2 className="w-5 h-5 text-green-500" /> : <XCircle className="w-5 h-5 text-red-500" />}
                  {isCorrectInPractice ? "Correct!" : `Incorrect. The answer is ${currentQuestion.correctAnswer}.`}
                </p>
                <p className="text-sm text-muted-foreground whitespace-pre-wrap">{currentQuestion.explanation}</p>
              </div>
            )}
          </CardContent>
        </Card>

        <div className="flex items-center justify-between">
          <Button variant="outline" onClick={handlePrevious} disabled={currentIndex === 0}>
            <ChevronLeft className="w-4 h-4 mr-1" /> Previous
          </Button>
          
          <Button
            variant={userAnswer?.flagged ? "destructive" : "ghost"}
            size="sm"
            onClick={() => handleFlagToggle(currentQuestion.id)}
          >
            <Flag className="w-4 h-4 mr-1" /> {userAnswer?.flagged ? "Flagged" : "Flag"}
          </Button>

          {currentIndex === filteredQuestions.length - 1 ? (
            <Button onClick={handleSubmit}>
              <Send className="w-4 h-4 mr-1" /> Submit Quiz
            </Button>
          ) : (
            <Button onClick={handleNext}>
              Next <ChevronRight className="w-4 h-4 ml-1" />
            </Button>
          )}
        </div>
      </div>
    );
  }

  // Review Screen
  if (quizState === "review") {
    const score = calculateScore();
    const breakdown = getBreakdown();

    return (
      <div className="container mx-auto px-4 py-8 max-w-4xl">
        <div className="text-center mb-8">
          <h1 className="text-4xl font-bold text-foreground mb-2">Quiz Complete!</h1>
          <p className="text-6xl font-bold text-primary">{score.correct}/{score.total}</p>
          <p className="text-2xl text-muted-foreground">{score.percentage}%</p>
        </div>

        <Card className="mb-6">
          <CardHeader><CardTitle>Score Breakdown</CardTitle></CardHeader>
          <CardContent>
            <div className="grid grid-cols-2 md:grid-cols-3 gap-3">
              {Object.entries(breakdown).map(([key, val]) => (
                <div key={key} className="p-3 bg-muted/50 rounded-lg text-center">
                  <p className="text-sm text-muted-foreground">{key}</p>
                  <p className="text-lg font-bold">{val.correct}/{val.total}</p>
                </div>
              ))}
            </div>
          </CardContent>
        </Card>

        <div className="space-y-6 mb-8">
          <h2 className="text-2xl font-bold">Review Answers</h2>
          {filteredQuestions.map((q, idx) => {
            const userAnswer = userAnswers.get(q.id);
            const isCorrect = q.type === "mcq" 
              ? userAnswer?.answer === q.correctAnswer 
              : userAnswer?.selfChecked;

            return (
              <Card key={q.id} className={isCorrect ? "border-green-500/30" : "border-red-500/30"}>
                <CardContent className="pt-6">
                  <div className="flex items-start justify-between mb-4">
                    <div className="flex items-center gap-2">
                      <span className="font-bold">Q{idx + 1}.</span>
                      {isCorrect ? <CheckCircle2 className="w-5 h-5 text-green-500" /> : <XCircle className="w-5 h-5 text-red-500" />}
                      {userAnswer?.flagged && <Flag className="w-4 h-4 text-yellow-500" />}
                    </div>
                    <div className="flex gap-2">
                      <Badge className={getDifficultyColor(q.difficulty)}>{q.difficulty}</Badge>
                      <Badge variant="outline">{q.topic}</Badge>
                    </div>
                  </div>

                  <p className="font-medium mb-4">{q.question}</p>

                  {q.type === "mcq" && q.options && (
                    <div className="space-y-2 mb-4">
                      {q.options.map((opt, i) => {
                        const letter = String.fromCharCode(65 + i);
                        const isUserAnswer = userAnswer?.answer === letter;
                        const isCorrectAnswer = q.correctAnswer === letter;
                        
                        let cls = "p-3 rounded-lg text-sm ";
                        if (isCorrectAnswer) cls += "bg-green-500/20 border border-green-500";
                        else if (isUserAnswer) cls += "bg-red-500/20 border border-red-500";
                        else cls += "bg-muted/30";

                        return (
                          <div key={i} className={cls}>
                            <span className="font-medium mr-2">{letter}.</span> {opt}
                            {isCorrectAnswer && <span className="ml-2 text-green-500">(Correct)</span>}
                            {isUserAnswer && !isCorrectAnswer && <span className="ml-2 text-red-500">(Your answer)</span>}
                          </div>
                        );
                      })}
                    </div>
                  )}

                  {q.type === "coding" && (
                    <div className="space-y-4 mb-4">
                      <div>
                        <p className="text-sm font-medium mb-2">Your Answer:</p>
                        <pre className="p-3 bg-muted rounded-lg text-sm font-mono whitespace-pre-wrap">{userAnswer?.answer || "(No answer)"}</pre>
                      </div>
                      <div>
                        <p className="text-sm font-medium mb-2">Model Answer:</p>
                        <pre className="p-3 bg-green-500/10 rounded-lg text-sm font-mono whitespace-pre-wrap">{q.correctAnswer}</pre>
                      </div>
                      {q.rubric && (
                        <div>
                          <p className="text-sm font-medium mb-2">Rubric:</p>
                          <ul className="list-disc list-inside text-sm text-muted-foreground space-y-1">
                            {q.rubric.map((r, i) => <li key={i}>{r}</li>)}
                          </ul>
                        </div>
                      )}
                      <div className="flex items-center gap-3 p-3 bg-muted/50 rounded-lg">
                        <input
                          type="checkbox"
                          id={`selfcheck-${q.id}`}
                          checked={userAnswer?.selfChecked || false}
                          onChange={(e) => handleSelfCheck(q.id, e.target.checked)}
                          className="w-4 h-4"
                        />
                        <Label htmlFor={`selfcheck-${q.id}`}>I matched the rubric (self-grade as correct)</Label>
                      </div>
                    </div>
                  )}

                  <div className="p-4 bg-muted/30 rounded-lg">
                    <p className="text-sm font-medium mb-2">Explanation:</p>
                    <p className="text-sm text-muted-foreground whitespace-pre-wrap">{q.explanation}</p>
                  </div>
                </CardContent>
              </Card>
            );
          })}
        </div>

        <div className="text-center">
          <Button onClick={handleRetry} size="lg">
            <RotateCcw className="w-5 h-5 mr-2" /> Retry Quiz
          </Button>
        </div>
      </div>
    );
  }

  return null;
};

export default Quiz;
