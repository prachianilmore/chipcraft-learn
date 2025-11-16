# Contributing to ChipLearn

Thank you for your interest in contributing to ChipLearn! This guide will help you add new learning modules to the platform.

## How to Add a New Module

### Step 1: Update `modules.json`

Add your module entry to `public/modules.json`:

```json
{
  "id": "07",
  "slug": "your-module-slug",
  "title": "Your Module Title",
  "description": "Brief description of your module",
  "difficulty": "Beginner|Intermediate|Advanced",
  "topics": ["Topic 1", "Topic 2", "Topic 3"],
  "completed": false
}
```

**Fields:**
- `id`: Sequential number (string format)
- `slug`: URL-friendly identifier (lowercase, hyphenated)
- `title`: Display name of the module
- `description`: One-sentence summary
- `difficulty`: Choose from Beginner, Intermediate, or Advanced
- `topics`: Array of 2-4 key topics covered
- `completed`: Always false for new modules

### Step 2: Create Module Content

Add your module details to `src/pages/ModuleDetail.tsx` in the `modulesData` object. Replace all TODO placeholders with actual content:

```javascript
"your-module-slug": {
  id: "07",
  title: "Your Module Title",
  description: "Brief description (replace 'To be added by contributor')",
  difficulty: "Beginner",
  topics: ["Topic 1", "Topic 2", "Topic 3"], // Replace TODO topics
  concept: "Detailed explanation of the concept (2-3 paragraphs). Replace 'TODO: Add concept explanation here'",
  exampleCode: `// Your SystemVerilog/Verilog code example
module your_module (
  input wire clk,
  output wire out
);
  // Implementation
endmodule

// Testbench
module tb_your_module;
  // Testbench code
endmodule`,
  expectedOutput: "Description of what the simulation should produce. Replace 'TODO: Describe expected simulation output'",
  quiz: [
    { question: "Your question? (replace TODO)", answer: "Expected answer (replace TODO)" },
    { question: "Another question? (replace TODO)", answer: "Another answer (replace TODO)" }
  ]
}
```

**Important**: Make sure to replace all placeholder text including:
- Module description
- Topic names
- Concept explanation
- Example code
- Expected output
- Quiz questions and answers

### Step 3: Test Your Module

1. Run the development server: `npm run dev`
2. Navigate to `/modules` and verify your card appears
3. Click "Start Module" and ensure all content displays correctly
4. Test the code in EDA Playground

### Step 4: Submit a Pull Request

1. Fork the ChipLearn repository
2. Create a feature branch: `git checkout -b module/your-module-name`
3. Commit your changes: `git commit -m "Add module: Your Module Title"`
4. Push to your fork: `git push origin module/your-module-name`
5. Open a Pull Request with:
   - Clear title: "Add Module: Your Module Title"
   - Description of what the module teaches
   - Any special testing notes

## Module Guidelines

- **Code Quality**: Ensure code examples are syntactically correct and follow best practices
- **Educational Value**: Focus on teaching concepts progressively
- **Testing**: Include working testbenches that demonstrate the concepts
- **Clarity**: Write clear explanations accessible to learners at the specified difficulty level
- **Length**: Keep modules focused (15-30 minutes completion time)

## Need Help?

- Open an issue for questions
- Join our community discussions
- Review existing modules for examples

---

**Powered by EDA Playground • Built by the CDF Open Education Team • 100% Open Source**
