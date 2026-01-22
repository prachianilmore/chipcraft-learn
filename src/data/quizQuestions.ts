export type QuestionType = "mcq" | "coding";
export type Difficulty = "Easy" | "Medium" | "Hard";
export type Topic = "Verilog" | "SystemVerilog" | "UVM" | "Assertions" | "Coverage" | "Debug" | "Coding";

export interface QuizQuestion {
  id: number;
  type: QuestionType;
  topic: Topic;
  difficulty: Difficulty;
  question: string;
  options?: string[];
  correctAnswer: string;
  explanation: string;
  codePrompt?: string;
  rubric?: string[];
}

export const quizQuestions: QuizQuestion[] = [
  {
    id: 1,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Easy",
    question: 'What is the main difference between "wire" and "logic" in SystemVerilog?',
    options: [
      "wire can store state, logic cannot",
      "logic can be driven by multiple continuous assignments",
      "logic can be driven by a single driver (procedural or continuous), wire is for nets",
      "They are identical in all cases"
    ],
    correctAnswer: "C",
    explanation: `The key difference lies in how they can be driven and their intended use:

• "wire" is a net type traditionally used for connecting structural elements. It requires continuous assignment (assign) or must be driven by module outputs. Multiple drivers are allowed (with resolution).

• "logic" is a 4-state data type that can be driven by either procedural assignments (always blocks) OR continuous assignments, but only by a single driver. This makes it more flexible for testbenches and modern RTL coding.

• Why A is wrong: Neither wire nor logic "stores state" in the traditional sense - flip-flops store state. Logic can hold a value in simulation, but this is not "state storage" like a register.

• Why B is wrong: This is backwards - wire can have multiple drivers with resolution, logic cannot.

• Why D is wrong: They have distinct synthesis and simulation semantics as explained above.

For synthesis, logic behaves like reg when driven procedurally, and like wire when driven with assign. The single-driver rule helps catch unintended multiple-driver bugs at compile time.`
  },
  {
    id: 2,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Easy",
    question: 'In SystemVerilog, what does "always_ff" enforce?',
    options: [
      "The block must contain only blocking assignments",
      "The block must model flip-flop behavior (sequential) with proper assignment rules",
      "The block is ignored by synthesis",
      "It forces asynchronous reset only"
    ],
    correctAnswer: "B",
    explanation: `always_ff is a specialized always block introduced in SystemVerilog specifically for modeling sequential (flip-flop) logic:

• It enforces that the block contains only non-blocking assignments (<=), which is the correct style for sequential logic to avoid race conditions.

• The sensitivity list must include edge-triggered events (posedge/negedge of clock, and optionally reset).

• Synthesis tools treat always_ff as a hint that this block should infer flip-flops, enabling better error checking.

• Why A is wrong: always_ff should use NON-blocking assignments (<=), not blocking (=). Using blocking assignments in always_ff is typically flagged as a lint/synthesis warning.

• Why C is wrong: always_ff is absolutely used by synthesis - it's the preferred way to describe flip-flops in modern RTL.

• Why D is wrong: always_ff works with both synchronous and asynchronous resets. The reset style depends on how you write the sensitivity list and if-else structure.

Using always_ff, always_comb, and always_latch instead of plain "always" provides better intent documentation and enables tools to catch common coding mistakes.`
  },
  {
    id: 3,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Medium",
    question: 'Which assertion is best to check "req implies eventually gnt within 1 to 3 cycles"?',
    options: [
      "req |-> ##[1:3] gnt",
      "req |=> gnt",
      "req ##[1:3] |-> gnt",
      "gnt |-> ##[1:3] req"
    ],
    correctAnswer: "A",
    explanation: `This question tests understanding of SVA (SystemVerilog Assertions) implication operators and timing:

• Option A (req |-> ##[1:3] gnt) is correct:
  - |-> is the overlapping implication operator
  - When req is true, check that gnt becomes true within 1 to 3 clock cycles
  - The ##[1:3] specifies a range delay of 1 to 3 cycles

• Why B is wrong: |=> is the non-overlapping implication (equivalent to |-> ##1). "req |=> gnt" means: if req is true, gnt must be true exactly one cycle later. No range, no flexibility.

• Why C is wrong: "req ##[1:3] |-> gnt" is syntactically problematic. The antecedent "req ##[1:3]" doesn't make clear sense - you'd be saying "req followed by 1-3 cycles of... nothing specific... implies gnt". This is not the intended behavior.

• Why D is wrong: This reverses cause and effect - it checks if gnt implies req will come later, which is the opposite of what we want.

Key insight: The implication operator evaluates the consequent only when the antecedent matches. The timing constraint belongs on the consequent side to specify when the response should occur.`
  },
  {
    id: 4,
    type: "mcq",
    topic: "UVM",
    difficulty: "Medium",
    question: "What is the primary role of a UVM sequencer?",
    options: [
      "Sample coverage",
      "Drive pins directly",
      "Arbitrates and provides sequence items to the driver",
      "Checks assertions"
    ],
    correctAnswer: "C",
    explanation: `The UVM sequencer is a crucial component in the UVM agent architecture that manages the flow of sequence items:

• The sequencer acts as an arbiter between multiple sequences that may be running concurrently, deciding which sequence gets to send its item next.

• It provides sequence items to the driver through a handshake mechanism (get_next_item/item_done or get/put).

• The sequencer maintains a FIFO or arbitration queue when multiple sequences are active.

• Why A is wrong: Coverage sampling is done by coverage collectors, typically in the subscriber/coverage component, not the sequencer. The sequencer deals with stimulus generation, not observation.

• Why B is wrong: The DRIVER drives pins directly by converting abstract sequence items into pin-level activity. The sequencer never touches DUT pins - it's purely about transaction-level management.

• Why D is wrong: Assertions are checked by the assertion library (SVA) or by checker/scoreboard components. The sequencer is on the stimulus side, not the checking side.

The typical flow is: Sequence → Sequencer → Driver → DUT interface pins. The sequencer is the "traffic controller" in the middle.`
  },
  {
    id: 5,
    type: "mcq",
    topic: "UVM",
    difficulty: "Medium",
    question: "Where should you typically compare expected vs actual transactions in UVM?",
    options: [
      "Driver",
      "Monitor + Scoreboard",
      "Sequencer",
      "Config DB"
    ],
    correctAnswer: "B",
    explanation: `Transaction comparison in UVM follows a clear architectural pattern:

• The Monitor observes DUT output pins and converts pin-level activity back into transaction objects. It broadcasts these "actual" transactions via an analysis port.

• The Scoreboard receives transactions from monitors (via analysis exports) and compares actual behavior against expected behavior. It maintains reference models or expected queues.

• This separation of concerns (Monitor observes, Scoreboard compares) keeps the architecture clean and reusable.

• Why A is wrong: The Driver's job is to DRIVE stimulus into the DUT, not to check responses. Drivers should be "blind" to whether transactions are correct - they just execute what sequences tell them.

• Why C is wrong: The Sequencer manages stimulus flow and arbitration. It doesn't see DUT outputs at all, so it cannot compare anything.

• Why D is wrong: uvm_config_db is a configuration mechanism for passing settings and handles between components. It's not a checking component - it's infrastructure for setup.

The correct pattern: Monitor extracts transactions → Analysis port → Scoreboard compares. The expected values might come from a reference model, a predictor component, or pre-computed expectations.`
  },
  {
    id: 6,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Medium",
    question: "What does functional coverage measure?",
    options: [
      "Toggle coverage of nets",
      "Whether all lines of code executed",
      "Whether specified scenarios/values were exercised",
      "Timing closure"
    ],
    correctAnswer: "C",
    explanation: `Functional coverage is a user-defined metric that measures whether specific design behaviors and scenarios have been tested:

• You define covergroups and coverpoints to specify WHAT you want to verify was exercised - specific register values, state machine transitions, protocol scenarios, corner cases, etc.

• It answers "Did my tests exercise the important functionality?" rather than "Did my tests touch every line of code?"

• Why A is wrong: Toggle coverage measures whether each signal transitioned both 0→1 and 1→0. This is a form of CODE/STRUCTURAL coverage, not functional coverage. It's automatic, not user-specified.

• Why B is wrong: Line/statement coverage measures code execution, which is also structural coverage. A test could execute all lines but miss critical functional scenarios (e.g., all error conditions, boundary values).

• Why D is wrong: Timing closure is a physical design concept related to meeting setup/hold requirements after place-and-route. It has nothing to do with verification coverage.

Functional coverage is essential because:
1. High code coverage doesn't guarantee you've tested what matters
2. It forces you to think about your verification plan explicitly
3. It provides measurable progress toward verification goals
4. Cross coverage can identify untested combinations`
  },
  {
    id: 7,
    type: "mcq",
    topic: "Debug",
    difficulty: "Medium",
    question: "A test passes alone but fails in regression. Most likely cause?",
    options: [
      "Deterministic seed",
      "Uninitialized state / test order dependency / shared resources",
      "Compiler bug always",
      "Too much coverage"
    ],
    correctAnswer: "B",
    explanation: `This is a classic regression debugging scenario that points to test isolation issues:

• Uninitialized state: If a test assumes certain initial conditions but doesn't set them explicitly, running after another test may leave unexpected values.

• Test order dependency: Tests may accidentally depend on side effects from previous tests (files created, global variables set, DUT state not fully reset).

• Shared resources: Tests competing for the same memory, files, or simulation resources can interfere with each other.

• Why A is wrong: A deterministic seed would make behavior REPEATABLE, not order-dependent. If anything, random seeds might cause different failures, but the standalone vs. regression difference points to contamination from other tests.

• Why C is wrong: If it were a compiler bug, the test would fail consistently, not only in regression. Compiler bugs are rare and wouldn't explain order-dependent behavior.

• Why D is wrong: Coverage collection doesn't affect test pass/fail behavior. "Too much coverage" isn't even a coherent problem - more coverage is always desirable.

Debug approach:
1. Identify which earlier test causes contamination
2. Check for proper reset/initialization at test start
3. Look for shared global state or files
4. Ensure DUT is fully reset between tests`
  },
  {
    id: 8,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Medium",
    question: 'What is the difference between "==" and "===" in SystemVerilog?',
    options: [
      "No difference",
      '"===" treats X/Z as wildcards',
      '"===" is case equality (X/Z must match exactly), "==" is logical equality with X-propagation',
      '"==" is only for strings'
    ],
    correctAnswer: "C",
    explanation: `Understanding equality operators is crucial for both simulation and debugging:

• "==" (logical equality): Returns X if either operand contains X or Z. This is "unknown-aware" - comparing 4'b1x0z == 4'b1x0z returns X, not 1.

• "===" (case equality): Compares all 4 states (0, 1, X, Z) literally. 4'b1x0z === 4'b1x0z returns 1 (true) because all bits match exactly, including X and Z positions.

• Why A is wrong: They have very different behavior with X/Z values, which is critical in verification environments where X's indicate problems.

• Why B is wrong: This describes ==?, the wildcard equality operator (where X/Z in the RIGHT operand are wildcards). Case equality === requires exact matching, not wildcarding.

• Why D is wrong: == works on all data types, not just strings. String comparison uses == just like numeric comparison.

Practical usage:
- Use == in RTL (synthesizable code) - X propagation is correct for hardware modeling
- Use === in testbenches when checking for specific unknown states
- Use ==? for wildcard matching in verification
- "!=" and "!==" are the inequality counterparts`
  },
  {
    id: 9,
    type: "mcq",
    topic: "UVM",
    difficulty: "Hard",
    question: "What is the purpose of the UVM factory?",
    options: [
      "Create waves",
      "Enable type/instance overrides for components/objects at runtime",
      "Increase simulation speed automatically",
      "Generate assertions"
    ],
    correctAnswer: "B",
    explanation: `The UVM factory is a powerful design pattern implementation that enables flexibility and reusability:

• Type overrides: Replace ALL instances of a class with a derived class. Example: Override base_driver with enhanced_driver across entire testbench.

• Instance overrides: Replace specific instances by hierarchical path. Example: Override only env.agent1.driver but keep env.agent2.driver as base type.

• Runtime configuration: Decide which class to instantiate based on test requirements, without modifying the original code.

• Enables testbench reuse: Same testbench code can use different component implementations for different tests.

• Why A is wrong: Waveform generation is done by the simulator ($dumpvars, VCD/FSDB dumping). The factory has nothing to do with waves.

• Why B is correct and powerful: You can write "create_component_by_type" and the factory decides what actually gets built. Tests can inject specialized behavior without editing the testbench.

• Why C is wrong: The factory doesn't affect simulation speed - it's a construction-time mechanism. If anything, there's tiny overhead for the lookup.

• Why D is wrong: Assertions are written in RTL/SVA. The factory manages UVM component/object instantiation, not assertion generation.

Key factory methods: create_object_by_type, create_component_by_type, set_type_override, set_inst_override.`
  },
  {
    id: 10,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Hard",
    question: "Why might an assertion pass vacuously?",
    options: [
      "Because the consequent is always true",
      "Because the antecedent never becomes true, so the implication is never tested",
      "Because reset is asserted",
      "Because coverage is off"
    ],
    correctAnswer: "B",
    explanation: `Vacuous passing is a subtle but critical concept in formal verification and simulation-based assertion checking:

• An implication assertion "A |-> B" passes vacuously when A (the antecedent) never becomes true during simulation/formal analysis.

• Logically, "if false then anything" is true - so the assertion technically passes, but it hasn't actually verified anything useful.

• This is dangerous because you might think your design is correct when really your trigger condition is broken.

• Why A is wrong: If the consequent is always true, the assertion passes NON-vacuously (it was actually tested and passed). Vacuous means the test was never really performed.

• Why C is wrong: During reset, assertions are typically disabled via a reset condition. This is different from vacuous passing - it's explicit disabling.

• Why D is wrong: Coverage being off doesn't affect assertion pass/fail - it only affects whether the pass/fail is recorded for coverage metrics.

How to detect vacuous passes:
1. Check assertion coverage - antecedent coverage should be non-zero
2. Many tools have "vacuity checking" options that report vacuous passes as warnings
3. Write cover properties for your antecedents to verify they actually occur

Example: "req |-> ##[1:3] gnt" passes vacuously if req is never asserted in your test.`
  },
  {
    id: 11,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Hard",
    question: "What is cross coverage?",
    options: [
      "Covering toggles across modules",
      "Combining two or more coverpoints to see combinations hit",
      "A type of assertion",
      "A lint rule"
    ],
    correctAnswer: "B",
    explanation: `Cross coverage is one of the most powerful functional coverage features in SystemVerilog:

• It creates a Cartesian product of two or more coverpoints and tracks which combinations have been hit.

• Example: If you have coverpoint A with bins {read, write} and coverpoint B with bins {size_1, size_2, size_4}, cross coverage tracks all 6 combinations (read+size_1, read+size_2, ..., write+size_4).

• This catches "corner case" combinations that might be missed if you only check individual coverpoints.

• You can exclude illegal or don't-care combinations using binsof with intersect or ignore_bins.

• Why A is wrong: Toggle coverage is structural (automatic), not functional. "Across modules" is not a coverage concept - cross coverage works within a covergroup.

• Why C is wrong: Cross coverage is part of the covergroup feature, not assertions. Assertions check behavior; coverage measures what was exercised.

• Why D is wrong: Lint rules are static code analysis. Cross coverage is dynamic (simulation-time) measurement.

Practical example:
covergroup cg;
  cp_cmd: coverpoint cmd {bins read = {0}; bins write = {1};}
  cp_size: coverpoint size {bins small = {[1:4]}; bins large = {[5:16]};}
  cx: cross cp_cmd, cp_size; // 2x2 = 4 cross bins
endgroup

This ensures you've tested both read and write with both small and large sizes.`
  },
  {
    id: 12,
    type: "mcq",
    topic: "Debug",
    difficulty: "Easy",
    question: "First step when you see a mismatch in scoreboard?",
    options: [
      "Randomly change seeds",
      "Immediately rewrite testbench",
      "Check monitor correctness + alignment of transaction boundaries/time",
      "Ignore it"
    ],
    correctAnswer: "C",
    explanation: `When debugging scoreboard mismatches, a systematic approach is essential:

• First verify your observation infrastructure is correct:
  - Is the monitor capturing data at the right clock edge?
  - Are transaction boundaries aligned between expected and actual?
  - Is there a timing mismatch (expected arrives before/after actual)?
  - Are you comparing the right transactions (sequence number, tag matching)?

• Why A is wrong: Randomly changing seeds won't help understand the root cause. Even if the failure disappears, the bug may still exist with other seeds. Always understand before "fixing."

• Why B is wrong: Rewriting the testbench without diagnosis is a waste of time and may introduce new bugs. The testbench might be correct - the DUT might have a bug!

• Why D is wrong: Never ignore failures. Even intermittent failures indicate real issues - race conditions, uninitialized values, or design bugs.

Debug workflow:
1. Check monitor correctness first (most common source of "false" mismatches)
2. Verify timing/alignment
3. Examine the specific transaction data
4. Trace backwards to find where expected and actual diverged
5. Determine if it's a TB bug or DUT bug
6. Add more debug visibility (assertions, prints, waveform markers)
7. Fix and verify with targeted tests`
  },
  {
    id: 13,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Medium",
    question: "What does non-blocking assignment (<=) help prevent in sequential logic?",
    options: [
      "Race conditions between flops in same clock edge",
      "Any and all X's",
      "Need for reset",
      "Makes logic combinational"
    ],
    correctAnswer: "A",
    explanation: `Non-blocking assignments are essential for correct sequential logic modeling:

• With non-blocking (<=), all right-hand sides are evaluated simultaneously at the clock edge, then all left-hand sides are updated. This prevents order-dependent behavior.

• With blocking (=), assignments happen sequentially - reading a value after it was assigned in the same block gives the NEW value, causing race conditions.

• Example that works correctly with <=:
  always_ff @(posedge clk) begin
    b <= a;  // Both see the OLD values
    c <= b;  // Creates a shift register
  end

• Same code with = would have c get the NEW value of b (which is a), breaking the shift register.

• Why B is wrong: Non-blocking doesn't prevent X's. X values come from uninitialized registers, multi-driver conflicts, or arithmetic with X's. You need proper reset and initialization to avoid X's.

• Why C is wrong: You still need reset! Non-blocking just prevents race conditions, it doesn't initialize values.

• Why D is wrong: Non-blocking is for SEQUENTIAL logic (flip-flops). Using <= in combinational logic is actually a mistake that may cause simulation/synthesis mismatch.

Rule of thumb: 
- always_ff (sequential): use <=
- always_comb (combinational): use =`
  },
  {
    id: 14,
    type: "mcq",
    topic: "UVM",
    difficulty: "Easy",
    question: "What does uvm_config_db primarily do?",
    options: [
      "Stores waveform dumps",
      "Pass configuration objects/values down the component hierarchy",
      "Generates random numbers",
      "Replaces the driver"
    ],
    correctAnswer: "B",
    explanation: `uvm_config_db is UVM's hierarchical configuration mechanism:

• It allows parent components (like tests or env) to set configuration values that child components can retrieve.

• Follows hierarchical scoping - you can target specific paths: uvm_config_db#(int)::set(this, "env.agent.*", "timeout", 1000);

• Supports any data type through parameterization: config_db#(int), config_db#(my_config), config_db#(virtual my_if)

• Common uses: passing virtual interfaces, configuration objects, enable/disable flags, timeout values

• Why A is wrong: Waveform dumping is a simulator feature ($dumpvars, VCD, FSDB), completely unrelated to UVM config.

• Why C is wrong: Random number generation is done by the SystemVerilog randomization engine (std::randomize, $urandom, object.randomize()). Config_db passes deterministic configuration.

• Why D is wrong: Replacing components is done by the UVM factory (set_type_override, set_inst_override), not config_db. Config_db passes data, factory creates objects.

Typical pattern:
// In test - set the config:
uvm_config_db#(my_config)::set(this, "env", "cfg", my_cfg);

// In env - get the config:
uvm_config_db#(my_config)::get(this, "", "cfg", cfg);`
  },
  {
    id: 15,
    type: "coding",
    topic: "SystemVerilog",
    difficulty: "Easy",
    question: 'Write a SystemVerilog snippet that detects a rising edge of signal "a" and generates a 1-cycle pulse "a_rise".',
    codePrompt: `// Write your code here
// Inputs: clk, rst_n, a
// Output: a_rise (1 when rising edge of 'a' detected)`,
    correctAnswer: `logic a_d; // Delayed version of 'a'

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    a_d <= 1'b0;
    a_rise <= 1'b0;
  end else begin
    a_d <= a;
    a_rise <= a & ~a_d; // High when a=1 and previous a=0
  end
end`,
    rubric: [
      "Uses a registered previous value (a_d or similar) to capture previous state",
      "Correct edge detection logic: a & ~a_d (current high AND previous low)",
      "Proper clocking with always_ff @(posedge clk)",
      "Includes reset handling for initialization",
      "Output a_rise is registered (1 cycle pulse, not combinational)",
      "Alternative: Could mention $rose() but that's typically for assertions, not synthesis"
    ],
    explanation: `Rising edge detection requires comparing current and previous values:

The key insight is that a rising edge occurs when:
- Current value of 'a' is 1 (high)
- Previous value of 'a' was 0 (low)

Implementation approach:
1. Register the previous value of 'a' into 'a_d' every clock cycle
2. Compare: a_rise = a & ~a_d

Why this works:
- When a transitions 0→1: a=1, a_d=0, so a & ~a_d = 1 & 1 = 1 (pulse!)
- When a stays 1: a=1, a_d=1, so a & ~a_d = 1 & 0 = 0 (no pulse)
- When a transitions 1→0 or stays 0: a=0, so a & ~a_d = 0 (no pulse)

Common mistakes:
- Forgetting to register a_d (causes combinational loop or incorrect timing)
- Using a_d <= a_rise instead of a_d <= a
- Not including reset (a_d would be X initially)
- Making a_rise combinational (may cause glitches)

Note: $rose(a) can be used in assertions to check for rising edges, but for synthesizable RTL that generates an output signal, the registered comparison method is standard.`
  },
  {
    id: 16,
    type: "coding",
    topic: "SystemVerilog",
    difficulty: "Medium",
    question: "Write a SystemVerilog task that waits for a signal 'valid' to be asserted (high) with a timeout. If 'valid' is not high within 100 clock cycles, print an error.",
    codePrompt: `// Write a task: wait_for_valid
// Should wait for 'valid' signal to go high
// Timeout after 100 clock cycles with error message`,
    correctAnswer: `task wait_for_valid(input logic clk, input logic valid);
  int timeout_count;
  timeout_count = 0;
  
  while (!valid && timeout_count < 100) begin
    @(posedge clk);
    timeout_count++;
  end
  
  if (!valid) begin
    $error("Timeout: 'valid' was not asserted within 100 cycles");
  end
endtask`,
    rubric: [
      "Uses a task with appropriate inputs (clk, valid at minimum)",
      "Implements a counter or fork-join timeout mechanism",
      "Checks valid signal in a loop or with event control",
      "Prints error/message on timeout condition",
      "Correctly waits on posedge clk for cycle counting",
      "Exits early if valid goes high before timeout"
    ],
    explanation: `This pattern is essential for testbench development:

Key concepts:
1. Tasks can consume simulation time (unlike functions)
2. Need to count clock cycles while monitoring the signal
3. Must handle both success (valid goes high) and failure (timeout) cases

The while loop approach:
- Check !valid (keep waiting while low)
- Also check timeout_count < 100 (stop waiting at limit)
- On each iteration, wait for a clock edge and increment counter
- After loop, check why we exited: was it valid or timeout?

Alternative approach using fork-join_any:
\`\`\`
fork
  begin  // Wait for valid
    @(posedge valid);
  end
  begin  // Timeout
    repeat(100) @(posedge clk);
    $error("Timeout...");
  end
join_any
disable fork;
\`\`\`

Common mistakes:
- Forgetting @(posedge clk) in the loop (infinite loop, hangs simulation)
- Not checking valid after the loop (can't distinguish success vs timeout)
- Using repeat(100) without checking valid in parallel (doesn't exit early)
- Off-by-one errors in counting

This timeout pattern is used extensively in UVM sequences and testbenches to prevent tests from hanging on unexpected conditions.`
  },
  {
    id: 17,
    type: "coding",
    topic: "SystemVerilog",
    difficulty: "Medium",
    question: "Write a simple 4-bit counter in SystemVerilog that counts up on each clock edge and wraps around. Include synchronous reset.",
    codePrompt: `// Module: counter_4bit
// Inputs: clk, rst (synchronous active-high)
// Output: count[3:0]`,
    correctAnswer: `module counter_4bit (
  input  logic       clk,
  input  logic       rst,
  output logic [3:0] count
);

  always_ff @(posedge clk) begin
    if (rst) begin
      count <= 4'b0000;
    end else begin
      count <= count + 1;  // Wraps automatically at 4 bits
    end
  end

endmodule`,
    rubric: [
      "Correct module declaration with clk, rst, and count ports",
      "Uses always_ff with posedge clk for sequential logic",
      "Implements SYNCHRONOUS reset (rst checked inside always_ff, not in sensitivity list)",
      "Count increments by 1 each cycle",
      "Natural wrap-around due to 4-bit width (or explicit check for 15)",
      "Uses non-blocking assignment (<=) for sequential logic"
    ],
    explanation: `This is a fundamental digital design building block:

Synchronous vs Asynchronous reset:
- Synchronous: Reset is checked at clock edge: always_ff @(posedge clk) if (rst)...
- Asynchronous: Reset in sensitivity list: always_ff @(posedge clk or posedge rst)

This example uses synchronous reset as specified.

Wrap-around behavior:
- 4'b1111 + 1 = 4'b0000 automatically due to bit width
- No explicit check needed unless you want different max count

Why use always_ff:
- Clearly indicates sequential (flip-flop) logic
- Tools can verify correct usage (non-blocking assignments, edge sensitivity)
- Better than generic "always" for synthesizable code

Common mistakes:
- Using blocking assignment (=) instead of non-blocking (<=)
- Using always_comb for a counter (counters are sequential!)
- Forgetting the module ports or using wrong widths
- Adding rst to sensitivity list when synchronous reset is intended

Extensions to consider:
- Enable signal (count only when enabled)
- Load value (parallel load)
- Up/down control
- Custom wrap value (count 0-9 for BCD)`
  },
  {
    id: 18,
    type: "coding",
    topic: "Coding",
    difficulty: "Medium",
    question: "Write a function that reverses a 32-bit input value (bit reversal, not byte reversal). For example, if input is 32'h80000001, output should be 32'h80000001 (bit 31 swaps with bit 0, bit 30 swaps with bit 1, etc.).",
    codePrompt: `// Function: bit_reverse
// Input: 32-bit value
// Output: bit-reversed 32-bit value`,
    correctAnswer: `function logic [31:0] bit_reverse(input logic [31:0] data);
  logic [31:0] result;
  for (int i = 0; i < 32; i++) begin
    result[31-i] = data[i];
  end
  return result;
endfunction`,
    rubric: [
      "Correct function declaration with 32-bit input and output",
      "Uses loop or explicit bit assignment for reversal",
      "Correct index mapping: result[31-i] = data[i] (or equivalent)",
      "Returns the reversed value",
      "Handles all 32 bits correctly",
      "Alternative: Could use streaming operators {<<{data}} in SystemVerilog"
    ],
    explanation: `Bit reversal is commonly needed in communication protocols (LSB-first vs MSB-first) and CRC calculations:

The algorithm:
- For each bit position i (0 to 31)
- Copy data[i] to result[31-i]
- This swaps bit 0 with 31, bit 1 with 30, etc.

Example trace with 8 bits for clarity:
- Input:  8'b10110001
- Output: 8'b10001101
- Bit 7 (1) → Bit 0
- Bit 6 (0) → Bit 1
- ... and so on

SystemVerilog streaming operator alternative:
\`\`\`
function logic [31:0] bit_reverse(input logic [31:0] data);
  return {<<{data}};  // Stream operator reverses bit order
endfunction
\`\`\`
The {<<{}} operator streams bits in reverse order - very compact!

Common mistakes:
- Off-by-one in loop bounds (using <= 32 instead of < 32)
- Wrong index formula (result[i] = data[31-i] also works, but be consistent)
- Byte reversal instead of bit reversal
- Not returning the result

Note: {<<8{data}} would reverse BYTE order (groups of 8 bits), which is different from bit reversal.`
  },
  {
    id: 19,
    type: "coding",
    topic: "Coding",
    difficulty: "Hard",
    question: "Write a function to find the index of the first '1' bit in a 16-bit input, scanning from LSB (bit 0). Return -1 if no bit is set. This is sometimes called 'find first set' or priority encoder logic.",
    codePrompt: `// Function: find_first_one
// Input: 16-bit value
// Output: index of first '1' from LSB (0-15), or -1 if all zeros`,
    correctAnswer: `function int find_first_one(input logic [15:0] data);
  for (int i = 0; i < 16; i++) begin
    if (data[i] == 1'b1) begin
      return i;
    end
  end
  return -1;  // No bit set
endfunction`,
    rubric: [
      "Correct function signature with 16-bit input and int/signed output",
      "Iterates from bit 0 (LSB) upward",
      "Returns immediately upon finding first '1'",
      "Returns -1 (or appropriate indicator) when no bit is set",
      "Uses early return for efficiency (doesn't continue after finding)",
      "Could also use $clog2 or casez for hardware implementation"
    ],
    explanation: `This 'find first set' (FFS) operation is fundamental in many designs:

Applications:
- Priority encoders (highest/lowest priority request)
- Floating point normalization (finding leading 1)
- Arbiter designs (which requestor gets access)
- Compression algorithms

The algorithm:
1. Scan from bit 0 to bit 15
2. Return immediately when first 1 is found
3. If loop completes, no 1 was found

For synthesizable hardware (priority encoder):
\`\`\`
always_comb begin
  casez (data)
    16'b???????????????1: result = 0;
    16'b??????????????10: result = 1;
    16'b?????????????100: result = 2;
    // ... continue pattern
    16'b1000000000000000: result = 15;
    default: result = -1;
  endcase
end
\`\`\`

Performance considerations:
- Software loop: O(n) worst case
- Hardware casez: Single cycle, but large MUX tree
- Optimized hardware: Divide-and-conquer with log(n) levels

Common mistakes:
- Scanning from MSB instead of LSB (would find LAST bit, not first)
- Not handling all-zeros case
- Using = instead of == for comparison
- Returning 0 instead of -1 for not-found (0 is a valid index!)`
  },
  {
    id: 20,
    type: "coding",
    topic: "UVM",
    difficulty: "Hard",
    question: "Sketch the structure of a simple UVM sequence that sends 5 random transactions of type 'my_transaction' to a sequencer. Show the main class structure and body task.",
    codePrompt: `// Class: my_sequence extends uvm_sequence
// Transaction type: my_transaction
// Send 5 random transactions`,
    correctAnswer: `class my_sequence extends uvm_sequence #(my_transaction);
  \`uvm_object_utils(my_sequence)
  
  function new(string name = "my_sequence");
    super.new(name);
  endfunction
  
  task body();
    my_transaction txn;
    
    repeat(5) begin
      txn = my_transaction::type_id::create("txn");
      start_item(txn);
      if (!txn.randomize()) begin
        \`uvm_error(get_type_name(), "Randomization failed")
      end
      finish_item(txn);
    end
  endtask
  
endclass`,
    rubric: [
      "Extends uvm_sequence with correct parameterization #(my_transaction)",
      "Uses `uvm_object_utils macro for factory registration",
      "Implements constructor with super.new()",
      "Implements body() task (not function)",
      "Uses start_item/finish_item pattern for each transaction",
      "Creates transaction using factory: type_id::create()",
      "Randomizes transaction between start_item and finish_item",
      "Has loop or repeat for 5 transactions"
    ],
    explanation: `This is the fundamental UVM stimulus generation pattern:

Key concepts:

1. uvm_sequence #(REQ) parameterization:
   - Binds the sequence to a transaction type
   - Enables start_item/finish_item for that type

2. \`uvm_object_utils:
   - Registers with UVM factory
   - Enables type overrides and create()
   - Sequences are objects (not components)

3. body() task:
   - Called by sequence.start(sequencer)
   - Contains the main stimulus generation logic
   - Must be a task (can consume time)

4. start_item/finish_item handshake:
   - start_item(txn): Request permission from sequencer, blocks until granted
   - (Randomize between start and finish)
   - finish_item(txn): Send to driver, blocks until driver signals item_done

5. Factory create:
   - txn = my_transaction::type_id::create("txn")
   - Enables type overrides if test wants different transaction class

Common mistakes:
- Forgetting to parameterize: uvm_sequence instead of uvm_sequence#(T)
- Using uvm_component_utils instead of uvm_object_utils
- Creating transaction outside the loop (reuses same object)
- Randomizing before start_item (sequence might want to modify)
- Using \`uvm_do macro without understanding what it does

The pattern: create → start_item → randomize → finish_item → repeat`
  },
  {
    id: 21,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Easy",
    question: "Which data type is used to model combinational connections between modules in Verilog?",
    options: [
      "reg",
      "integer",
      "wire",
      "logic"
    ],
    correctAnswer: "C",
    explanation: `In Verilog, a wire represents a physical connection and is driven continuously.
It is commonly used for module interconnections and combinational logic.
A reg is used inside procedural blocks and does not represent a physical wire.
Using the wrong type can cause synthesis or simulation mismatches.`
  },
  {
    id: 22,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Easy",
    question: "Where can a reg data type be assigned in Verilog?",
    options: [
      "Continuous assign statements",
      "always or initial blocks",
      "Module port connections only",
      "Only inside functions"
    ],
    correctAnswer: "B",
    explanation: `A reg can be assigned only inside procedural blocks such as always or initial.
It cannot be driven by continuous assign statements.
This makes reg suitable for modeling storage or procedural behavior.
Despite the name, reg does not always imply hardware registers.`
  },
  {
    id: 23,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Medium",
    question: "What happens if multiple always blocks drive the same reg?",
    options: [
      "Last assignment wins",
      "Synthesis automatically resolves it",
      "Causes a multiple driver conflict",
      "It becomes a wire"
    ],
    correctAnswer: "C",
    explanation: `A reg must have exactly one procedural driver.
Multiple always blocks driving the same reg cause conflicts and undefined behavior.
Most simulators will flag this as an error.
This is a common beginner mistake in RTL design.`
  },
  {
    id: 24,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Medium",
    question: "Which sensitivity list is correct for modeling combinational logic?",
    options: [
      "@(posedge clk)",
      "@(a or b or c)",
      "@(negedge clk)",
      "@(posedge reset)"
    ],
    correctAnswer: "B",
    explanation: `Combinational logic must react to changes in all its inputs.
Using @(a or b or c) ensures the block re-evaluates whenever inputs change.
Clock edges are used only for sequential logic.
Missing signals in sensitivity lists can cause simulation mismatches.`
  },
  {
    id: 25,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Medium",
    question: "What does the following code infer?\nalways @(posedge clk)\n  q <= d;",
    options: [
      "Latch",
      "Combinational logic",
      "Flip-flop",
      "Tri-state buffer"
    ],
    correctAnswer: "C",
    explanation: `Using posedge clk with nonblocking assignment infers a flip-flop.
This is the standard way to model sequential storage in Verilog.
Latches occur when incomplete assignments are used in combinational blocks.
This pattern is synthesis-friendly and widely used.`
  },
  {
    id: 26,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Hard",
    question: "Why are blocking assignments (=) discouraged in clocked always blocks?",
    options: [
      "They cause syntax errors",
      "They prevent synthesis",
      "They can create race conditions",
      "They use more hardware"
    ],
    correctAnswer: "C",
    explanation: `Blocking assignments execute immediately and can create race conditions
between sequential elements evaluated in the same clock edge.
Nonblocking assignments schedule updates simultaneously, modeling real hardware.
This is why <= is recommended for clocked logic.`
  },
  {
    id: 27,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Easy",
    question: "What does an 'initial' block do in Verilog RTL?",
    options: [
      "Runs repeatedly on every clock edge",
      "Executes once at time 0 (simulation start)",
      "Synthesizes into flip-flops",
      "Replaces always blocks"
    ],
    correctAnswer: "B",
    explanation: `"initial" blocks begin execution at simulation time 0 and run once.
They are commonly used in testbenches for stimulus and initialization.
In synthesizable RTL, initial usage is limited or tool-dependent.
For hardware modeling, sequential logic is normally written using always @(posedge clk).`
  },
  {
    id: 28,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Medium",
    question: "Which is the best SystemVerilog construct for combinational logic with automatic sensitivity?",
    options: [
      "always @(posedge clk)",
      "always @(*)",
      "always_comb",
      "initial"
    ],
    correctAnswer: "C",
    explanation: `always_comb is designed specifically for combinational logic.
It automatically includes all RHS signals in the sensitivity list and adds extra checks.
It helps prevent missing sensitivity list bugs and improves clarity.
always @(*) is similar, but always_comb provides stronger semantic enforcement.`
  },
  {
    id: 29,
    type: "mcq",
    topic: "UVM",
    difficulty: "Medium",
    question: "Which UVM component typically converts pin-level activity into transactions?",
    options: [
      "Sequencer",
      "Driver",
      "Monitor",
      "Test"
    ],
    correctAnswer: "C",
    explanation: `A monitor passively observes interface signals and reconstructs meaningful transactions.
It does not drive the DUT; it samples activity and publishes transactions via analysis ports.
Drivers actively drive signals, sequencers provide items to drivers, and tests control the environment.
Monitors are essential for scoreboards and coverage collection.`
  },
  {
    id: 30,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Medium",
    question: "What does 'disable iff (reset)' do in an SVA property?",
    options: [
      "Forces reset to be synchronous",
      "Turns off the assertion checking while reset is true",
      "Makes the assertion check only during reset",
      "Converts assertion into coverage"
    ],
    correctAnswer: "B",
    explanation: `disable iff(reset) prevents the assertion from evaluating when reset is asserted.
This avoids false failures during reset behavior and initialization.
It is commonly used for protocol checks that are only valid outside reset.
It does not change reset type; it only gates assertion evaluation.`
  },
  {
    id: 31,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Medium",
    question: "Why do we use bins in functional coverage?",
    options: [
      "To speed up synthesis",
      "To group values/scenarios we want to track as hits",
      "To reduce clock frequency",
      "To replace assertions"
    ],
    correctAnswer: "B",
    explanation: `Bins allow you to define which values or ranges should be tracked in a coverpoint.
They map verification intent (important scenarios) into measurable coverage goals.
You can also use bins to ignore or focus on certain value sets.
This helps ensure your test plan is actually exercised.`
  },
  {
    id: 32,
    type: "mcq",
    topic: "Debug",
    difficulty: "Easy",
    question: "When debugging an intermittent failure, what is the BEST first action?",
    options: [
      "Immediately rewrite the DUT",
      "Re-run with the same seed and capture a waveform/log",
      "Disable all assertions",
      "Increase randomization only"
    ],
    correctAnswer: "B",
    explanation: `First make the issue reproducible by re-running with the same seed.
Then capture waveforms and logs to identify where behavior diverges.
Without reproducibility, debug becomes guesswork.
Assertions and logging help narrow the failure point quickly.`
  },
  {
    id: 33,
    type: "coding",
    topic: "Coding",
    difficulty: "Medium",
    question: "Self-check: Write pseudocode (or any language) to find if an array contains any duplicate number.",
    rubric: [
      "Use a set/hashmap OR sorting approach",
      "Explain time complexity",
      "Handle empty/1-element arrays"
    ],
    correctAnswer: "Use a set. For each element x: if x in set return true; else add x. Return false at end.",
    explanation: `A set-based approach detects duplicates in O(n) expected time.
Sorting also works in O(n log n) then checking neighbors.
In DV interviews, explaining complexity + edge cases matters as much as code.
This is a common warm-up logic question.`
  },
  // ========== NEW VERILOG QUESTIONS (8 more to reach 15) ==========
  {
    id: 34,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Easy",
    question: "What is the default value of an uninitialized reg in Verilog simulation?",
    options: [
      "0",
      "1",
      "X (unknown)",
      "Z (high-impedance)"
    ],
    correctAnswer: "C",
    explanation: `In Verilog simulation, uninitialized reg variables default to X (unknown state).
This helps designers identify missing initialization during simulation.
In synthesis, FPGAs may initialize to 0, but ASICs have undefined power-on states.
Always use explicit reset logic to ensure deterministic behavior in hardware.`
  },
  {
    id: 35,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Medium",
    question: "What causes an unintentional latch to be inferred in combinational logic?",
    options: [
      "Using wire instead of reg",
      "Missing assignments for some conditions in always @(*)",
      "Using posedge clk sensitivity",
      "Using nonblocking assignments"
    ],
    correctAnswer: "B",
    explanation: `Latches are inferred when a combinational always block doesn't assign a value in all paths.
For example, an if statement without an else clause creates a latch for the missing condition.
The synthesizer must preserve the previous value when no new value is specified.
Always assign default values at the start of combinational blocks to avoid latches.`
  },
  {
    id: 36,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Medium",
    question: "What problem can occur if you forget a signal in a combinational always block's sensitivity list?",
    options: [
      "The code won't compile",
      "Synthesis fails completely",
      "Simulation and synthesis behavior may differ",
      "The signal becomes a latch"
    ],
    correctAnswer: "C",
    explanation: `Missing signals in sensitivity lists cause simulation/synthesis mismatch.
In simulation, the block won't trigger when the missing signal changes.
Synthesis tools infer combinational logic from the code structure, ignoring the sensitivity list.
Use @(*) or always_comb to automatically include all signals and avoid this issue.`
  },
  {
    id: 37,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Hard",
    question: "What is a race condition in Verilog and when does it typically occur?",
    options: [
      "When two modules have the same name",
      "When blocking assignments in different always blocks access the same variable at the same time",
      "When the clock frequency is too high",
      "When wire and reg are mixed"
    ],
    correctAnswer: "B",
    explanation: `Race conditions occur when the order of execution affects the result, but that order is undefined.
Using blocking assignments (=) in multiple clocked always blocks accessing the same signals causes races.
The simulator may execute blocks in different orders, producing inconsistent results.
Use nonblocking assignments (<=) in clocked logic to ensure all reads happen before writes.`
  },
  {
    id: 38,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Hard",
    question: "Which reset coding style is recommended for ASIC designs?",
    options: [
      "Only initial blocks for reset",
      "Asynchronous reset with synchronous de-assertion",
      "No reset, rely on power-on state",
      "Random reset values for security"
    ],
    correctAnswer: "B",
    explanation: `Asynchronous reset with synchronous de-assertion is the industry standard for ASICs.
Async reset ensures immediate reset regardless of clock, which is critical for power-on.
Synchronous de-assertion prevents metastability when coming out of reset.
This is implemented with a reset synchronizer that releases reset aligned to the clock.`
  },
  {
    id: 39,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Medium",
    question: "What is the key difference between 'initial' and 'always' blocks for synthesis?",
    options: [
      "No difference, both synthesize identically",
      "initial is for testbenches only; always describes synthesizable hardware",
      "always is deprecated in modern tools",
      "initial runs faster in simulation"
    ],
    correctAnswer: "B",
    explanation: `The 'always' block describes hardware behavior and is the primary synthesizable construct.
The 'initial' block is intended for simulation/testbench code and generally not synthesizable.
Some FPGA tools support initial for setting power-on values, but this is not portable to ASICs.
For synthesizable RTL, always use 'always' with proper reset logic for initialization.`
  },
  {
    id: 40,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Hard",
    question: "When might simulation show correct behavior but synthesis produce wrong hardware?",
    options: [
      "When using standard Verilog operators",
      "When sensitivity list is incomplete or blocking/nonblocking assignments are misused",
      "When using too many modules",
      "When wire widths are specified"
    ],
    correctAnswer: "B",
    explanation: `Simulation/synthesis mismatches commonly occur due to sensitivity list issues and assignment misuse.
Incomplete sensitivity lists make simulation miss events but synthesis infers all combinational inputs.
Using blocking in sequential or nonblocking in combinational logic creates different behaviors.
Always follow coding guidelines: @(*) or always_comb for combinational, <= for sequential.`
  },
  {
    id: 41,
    type: "mcq",
    topic: "Verilog",
    difficulty: "Easy",
    question: "What keyword is used for continuous assignment to a wire in Verilog?",
    options: [
      "always",
      "initial",
      "assign",
      "drive"
    ],
    correctAnswer: "C",
    explanation: `The 'assign' keyword creates a continuous assignment that drives a wire.
The wire value is continuously updated whenever the right-hand side expression changes.
This is different from procedural assignments which only update in always/initial blocks.
Continuous assignments model combinational connections between modules and logic.`
  },
  // ========== NEW SYSTEMVERILOG QUESTIONS (7 more to reach 15) ==========
  {
    id: 42,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Easy",
    question: "What is the main advantage of 'logic' over 'reg' and 'wire' in SystemVerilog?",
    options: [
      "logic is faster in simulation",
      "logic can be driven by either procedural or continuous assignments (but not both)",
      "logic only supports 2-state values",
      "logic is required for synthesis"
    ],
    correctAnswer: "B",
    explanation: `The 'logic' type unifies reg and wire, reducing confusion about which to use.
It can be driven by assign statements or procedural blocks, but only one driver is allowed.
This single-driver rule helps catch multiple-driver bugs at compile time.
'logic' is a 4-state type (0, 1, X, Z), making it compatible with verification and synthesis.`
  },
  {
    id: 43,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Medium",
    question: "What is the difference between packed and unpacked arrays in SystemVerilog?",
    options: [
      "Packed arrays are stored as contiguous bits; unpacked arrays are separate elements",
      "Unpacked arrays are faster",
      "Packed arrays cannot be synthesized",
      "There is no difference"
    ],
    correctAnswer: "A",
    explanation: `Packed arrays store all bits contiguously and can be treated as a single vector.
Example: logic [3:0][7:0] packed_data; // 32 bits stored together
Unpacked arrays store elements separately, like an array of objects.
Example: logic [7:0] unpacked_data[4]; // 4 separate 8-bit elements
Packed arrays are useful for bit manipulation; unpacked for memory modeling.`
  },
  {
    id: 44,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Medium",
    question: "What does 'typedef enum' provide in SystemVerilog?",
    options: [
      "Faster simulation speed",
      "Named constants with type safety for state machines and configuration",
      "Automatic reset generation",
      "Waveform annotation only"
    ],
    correctAnswer: "B",
    explanation: `typedef enum creates user-defined enumerated types with meaningful names.
It improves code readability and provides type checking at compile time.
Enumerated values are automatically assigned incrementing integers unless specified.
Commonly used for FSM states: typedef enum {IDLE, RUN, DONE} state_t;
Waveform viewers display enum names instead of raw numbers, aiding debug.`
  },
  {
    id: 45,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Hard",
    question: "What does the 'automatic' keyword do for variables in SystemVerilog tasks/functions?",
    options: [
      "Makes variables persistent across calls",
      "Allocates fresh storage for each call, enabling recursion and reentrancy",
      "Increases simulation speed",
      "Forces synthesis to use RAM"
    ],
    correctAnswer: "B",
    explanation: `By default, task/function variables are static, shared across all calls.
The 'automatic' keyword allocates new storage for each call (like stack variables in C).
This is required for recursive functions and reentrant tasks in concurrent testbenches.
Without automatic, calling a task while it's still running corrupts its local variables.
Use 'automatic' for tasks called from multiple threads or with recursive algorithms.`
  },
  {
    id: 46,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Medium",
    question: "What is the purpose of an 'interface' in SystemVerilog?",
    options: [
      "To replace modules entirely",
      "To bundle related signals and simplify port connections between modules",
      "To increase clock frequency",
      "To disable assertions"
    ],
    correctAnswer: "B",
    explanation: `Interfaces bundle related signals (like a bus protocol) into a single unit.
They simplify module ports: instead of listing 20 signals, connect one interface.
Interfaces can include modports to specify signal directions for different users.
They can also contain tasks, functions, and assertions related to the protocol.
Example: An AXI interface bundles address, data, and handshake signals together.`
  },
  {
    id: 47,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Hard",
    question: "What constraint does always_ff enforce that plain 'always' does not?",
    options: [
      "Must use blocking assignments",
      "Must have edge-sensitive trigger and should use nonblocking assignments",
      "Cannot include if statements",
      "Must have a reset signal"
    ],
    correctAnswer: "B",
    explanation: `always_ff requires a sensitivity list with edge events (posedge/negedge).
Tools check that only nonblocking assignments (<=) are used, flagging blocking as a warning.
This enforces the correct coding style for flip-flop inference.
Unlike plain 'always', which allows any style, always_ff makes design intent explicit.
This helps catch common mistakes and improves code quality and tool optimization.`
  },
  {
    id: 48,
    type: "mcq",
    topic: "SystemVerilog",
    difficulty: "Easy",
    question: "How does 'always_comb' differ from 'always @(*)'?",
    options: [
      "always_comb is slower",
      "always_comb executes at time 0 and checks for latches; always @(*) does not",
      "always @(*) is not synthesizable",
      "They are completely identical"
    ],
    correctAnswer: "B",
    explanation: `always_comb has stronger semantics than always @(*).
It automatically executes once at time 0 to initialize outputs.
It checks that the block doesn't infer latches (warns if assignments are incomplete).
It verifies no other process writes to the same variables.
always @(*) only provides automatic sensitivity but lacks these extra checks.`
  },
  // ========== NEW UVM QUESTIONS (9 more to reach 15) ==========
  {
    id: 49,
    type: "mcq",
    topic: "UVM",
    difficulty: "Easy",
    question: "What is the main difference between uvm_component and uvm_object?",
    options: [
      "uvm_component is for testbenches only",
      "uvm_object has phases; uvm_component does not",
      "uvm_component has phases and hierarchy; uvm_object is for data/transactions",
      "They are identical"
    ],
    correctAnswer: "C",
    explanation: `uvm_component forms the testbench hierarchy and participates in UVM phases.
It has a parent-child relationship, build_phase, run_phase, etc.
uvm_object is lightweight, used for transactions, sequences, and configuration objects.
uvm_object has no hierarchy or phases - it's created and destroyed dynamically.
Rule: Use uvm_component for structural elements, uvm_object for data items.`
  },
  {
    id: 50,
    type: "mcq",
    topic: "UVM",
    difficulty: "Medium",
    question: "What is the purpose of the build_phase in UVM?",
    options: [
      "To run stimulus on the DUT",
      "To create and configure child components in the hierarchy",
      "To compare expected vs actual results",
      "To generate waveforms"
    ],
    correctAnswer: "B",
    explanation: `build_phase is for constructing and configuring the testbench component hierarchy.
Parent components create their children using type_id::create() in this phase.
Configuration is retrieved via uvm_config_db::get() during build.
build_phase executes top-down: parent builds before children.
No stimulus runs here - that happens in run_phase after all components are built.`
  },
  {
    id: 51,
    type: "mcq",
    topic: "UVM",
    difficulty: "Medium",
    question: "How does the sequencer-driver handshake work in UVM?",
    options: [
      "Driver pushes items to sequencer",
      "Driver calls get_next_item, processes it, then calls item_done",
      "Sequencer directly drives DUT pins",
      "No handshake is needed"
    ],
    correctAnswer: "B",
    explanation: `The driver requests transactions by calling seq_item_port.get_next_item(req).
This blocks until the sequencer provides an item from an active sequence.
The driver then converts the transaction to pin-level activity on the DUT interface.
After driving completes, the driver calls seq_item_port.item_done() to signal completion.
This handshake ensures proper flow control between sequences and drivers.`
  },
  {
    id: 52,
    type: "mcq",
    topic: "UVM",
    difficulty: "Easy",
    question: "What is the primary role of a UVM monitor?",
    options: [
      "Drive stimulus to DUT",
      "Observe DUT signals and convert to transactions for analysis",
      "Generate random test cases",
      "Control test execution"
    ],
    correctAnswer: "B",
    explanation: `Monitors passively observe DUT interface signals without driving them.
They reconstruct pin-level activity into transaction-level objects.
These transactions are broadcast via analysis ports to subscribers.
Scoreboards and coverage collectors connect to monitor analysis ports.
Monitors must be passive - driving is the driver's responsibility.`
  },
  {
    id: 53,
    type: "mcq",
    topic: "UVM",
    difficulty: "Medium",
    question: "What is the purpose of a UVM scoreboard?",
    options: [
      "To sequence transactions",
      "To compare expected vs actual transactions and report mismatches",
      "To configure the DUT",
      "To generate clock signals"
    ],
    correctAnswer: "B",
    explanation: `The scoreboard is the central checking component in a UVM environment.
It receives actual transactions from monitors via analysis ports.
Expected results come from a reference model, predictor, or pre-computed values.
When expected and actual don't match, the scoreboard reports errors.
This separation of monitoring and checking improves reusability and clarity.`
  },
  {
    id: 54,
    type: "mcq",
    topic: "UVM",
    difficulty: "Medium",
    question: "What is uvm_analysis_port used for?",
    options: [
      "Driving DUT inputs",
      "Broadcasting transactions to multiple subscribers without blocking",
      "Storing configuration data",
      "Replacing the driver"
    ],
    correctAnswer: "B",
    explanation: `uvm_analysis_port is a broadcast mechanism for one-to-many communication.
Monitors use it to publish observed transactions to any number of subscribers.
Subscribers (scoreboards, coverage) connect via analysis_export or analysis_imp.
The write() method broadcasts to all connected components simultaneously.
It's non-blocking - the monitor doesn't wait for subscribers to process.`
  },
  {
    id: 55,
    type: "mcq",
    topic: "UVM",
    difficulty: "Hard",
    question: "What is the purpose of objections in UVM?",
    options: [
      "To reject bad transactions",
      "To control when phases end by indicating pending work",
      "To override components",
      "To raise assertion failures"
    ],
    correctAnswer: "B",
    explanation: `Objections coordinate phase completion in UVM's phased execution.
A component raises an objection to indicate it has work pending.
The phase doesn't end until all objections are dropped.
Sequences typically raise objection at start and drop when done sending items.
Without objections, the run_phase would end immediately with no stimulus.
Example: phase.raise_objection(this); ... phase.drop_objection(this);`
  },
  {
    id: 56,
    type: "mcq",
    topic: "UVM",
    difficulty: "Hard",
    question: "What does the UVM factory allow you to do?",
    options: [
      "Create faster simulations",
      "Substitute component types at runtime without changing code",
      "Generate waveforms automatically",
      "Replace the simulator"
    ],
    correctAnswer: "B",
    explanation: `The factory enables type and instance overrides for components and objects.
Type override: Replace all instances of ClassA with ClassB globally.
Instance override: Replace a specific instance by hierarchical path.
This allows tests to inject specialized behavior without modifying the testbench.
All components must use type_id::create() instead of new() to enable overrides.
Example: factory.set_type_override_by_type(base_drv::get_type(), custom_drv::get_type());`
  },
  {
    id: 57,
    type: "mcq",
    topic: "UVM",
    difficulty: "Hard",
    question: "When is uvm_config_db::set() typically called?",
    options: [
      "In the run_phase after stimulus completes",
      "In the test's build_phase before children are built",
      "In the final_phase",
      "Only in the driver"
    ],
    correctAnswer: "B",
    explanation: `uvm_config_db::set() is typically called in build_phase before child components build.
This ensures configuration is available when children call get() in their build_phase.
The test sets configuration first, then env, then agents - following the build order.
If set() happens after get(), the child won't receive the value.
Common uses: virtual interfaces, configuration objects, enable flags, timeout values.`
  },
  // Assertions Questions (12 new questions to reach 15 total)
  {
    id: 58,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Easy",
    question: "What is the difference between immediate and concurrent assertions in SVA?",
    options: [
      "Immediate assertions are checked over multiple clock cycles, concurrent are checked instantly",
      "Immediate assertions are checked instantly like procedural statements, concurrent are clock-based and span time",
      "There is no difference, they are interchangeable",
      "Concurrent assertions cannot have implications"
    ],
    correctAnswer: "B",
    explanation: `Immediate assertions (assert) are checked at the exact moment the statement executes.
They behave like procedural if-statements and are used inside always blocks or initial blocks.
Concurrent assertions (assert property) are evaluated over time based on clock edges.
They can span multiple cycles and use temporal operators like ##, |-> and |=>.
Immediate: assert(a == b); Concurrent: assert property(@(posedge clk) a |-> b);
Concurrent assertions are the core of SVA for protocol and timing checks.`
  },
  {
    id: 59,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Easy",
    question: "What does the ## operator represent in SVA?",
    options: [
      "Logical AND between signals",
      "A clock cycle delay between sequence elements",
      "A comment marker",
      "Signal inversion"
    ],
    correctAnswer: "B",
    explanation: `The ## operator specifies clock cycle delays between sequence elements.
##1 means one clock cycle delay, ##3 means three cycles delay.
##[1:4] specifies a range - the next event can occur 1 to 4 cycles later.
##[0:$] means zero to infinite cycles (eventually, unbounded).
Example: req ##[1:3] gnt means gnt follows req within 1 to 3 cycles.
This is fundamental for expressing timing relationships in protocols.`
  },
  {
    id: 60,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Easy",
    question: "What does $rose(signal) check in SVA?",
    options: [
      "That the signal is always high",
      "That the signal transitioned from 0 to 1 on this clock edge",
      "That the signal is at a high voltage level",
      "That the signal has been high for multiple cycles"
    ],
    correctAnswer: "B",
    explanation: `$rose(signal) returns true when the signal transitions from 0 to 1.
It compares the sampled value at the current clock to the previous clock.
$fell(signal) is the opposite - detects 1-to-0 transitions.
$stable(signal) returns true when the signal hasn't changed.
These are sampled value functions - they work on the sampled (preponed) values.
Common use: assert property(@(posedge clk) $rose(valid) |-> data_ready);`
  },
  {
    id: 61,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Easy",
    question: "What is the purpose of 'cover property' in SVA?",
    options: [
      "To fail simulation when a property is true",
      "To track whether a property scenario was observed during simulation",
      "To hide properties from waveform viewers",
      "To replace assertions with print statements"
    ],
    correctAnswer: "B",
    explanation: `cover property tracks whether a scenario occurred during simulation.
Unlike assert (which fails on violation), cover simply records hits.
This is used for functional coverage - did we exercise this scenario?
Coverage results show if your tests actually triggered important behaviors.
Example: cover property(@(posedge clk) req ##[1:3] gnt); tracks req-to-gnt handshakes.
High assertion coverage but low cover property hits indicates incomplete testing.`
  },
  {
    id: 62,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Easy",
    question: "What does 'disable iff' do in an SVA property?",
    options: [
      "Permanently removes the assertion from simulation",
      "Disables assertion checking while the specified condition is true",
      "Enables the assertion only during reset",
      "Converts the assertion into a cover property"
    ],
    correctAnswer: "B",
    explanation: `disable iff(condition) suspends assertion evaluation when condition is true.
Most commonly used with reset: disable iff(reset) to avoid false failures during reset.
When disabled, the assertion doesn't fail or pass - it's simply not evaluated.
This prevents spurious failures during initialization or special modes.
Syntax: assert property(@(posedge clk) disable iff(rst) a |-> b);
The condition is evaluated asynchronously, not sampled with the clock.`
  },
  {
    id: 63,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Medium",
    question: "What is the difference between |-> and |=> in SVA?",
    options: [
      "|-> is for properties, |=> is for sequences",
      "|-> is overlapping implication (same cycle), |=> is non-overlapping (next cycle)",
      "|-> is blocking, |=> is non-blocking",
      "They are identical in behavior"
    ],
    correctAnswer: "B",
    explanation: `|-> (overlapping implication) evaluates the consequent starting the same cycle the antecedent matches.
|=> (non-overlapping implication) evaluates the consequent starting one cycle after the antecedent matches.
|=> is equivalent to |-> ##1 (implication plus one cycle delay).
Example: req |-> gnt checks gnt on the same cycle req is true.
Example: req |=> gnt checks gnt one cycle after req is true.
This distinction is critical for specifying correct protocol timing in assertions.`
  },
  {
    id: 64,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Medium",
    question: "What is a 'vacuous pass' in SVA?",
    options: [
      "When an assertion passes because the antecedent was never true",
      "When an assertion passes after being disabled",
      "When an assertion has a syntax error but doesn't fail",
      "When coverage reaches 100%"
    ],
    correctAnswer: "A",
    explanation: `A vacuous pass occurs when the implication's antecedent (left side) is never true.
In logic: if the condition is false, the implication is trivially true.
Example: req |-> gnt - if req is never asserted, the assertion always passes vacuously.
This can hide bugs: your check "passes" but was never actually tested.
Tools can report vacuous passes to flag untested assertions.
Mitigation: use cover property to verify the antecedent scenario occurs.
Interviewers often ask this to test understanding of implication semantics.`
  },
  {
    id: 65,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Medium",
    question: "What is the difference between a sequence and a property in SVA?",
    options: [
      "Sequences can only contain one signal, properties can contain multiple",
      "Sequences describe temporal patterns, properties add checking semantics like implication",
      "Properties are faster to simulate than sequences",
      "Sequences are for coverage, properties are for debugging"
    ],
    correctAnswer: "B",
    explanation: `Sequences describe temporal patterns of signals over time using ##, |, and other operators.
Properties wrap sequences and add checking semantics like implication (|->), disable iff, etc.
Sequences alone cannot be asserted - they must be wrapped in a property.
sequence s1: a ##1 b ##1 c;  // just a pattern
property p1: @(posedge clk) req |-> s1;  // adds checking
assert property(p1);  // now we can assert it
This separation allows reusing sequences in multiple properties with different checks.`
  },
  {
    id: 66,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Medium",
    question: "In SVA, what does ##[0:$] represent?",
    options: [
      "Exactly zero clock cycles",
      "Zero to infinite clock cycles (eventually)",
      "Invalid syntax that causes compilation error",
      "Dollar amount of simulation time"
    ],
    correctAnswer: "B",
    explanation: `##[0:$] means zero to unbounded (infinite) clock cycle delay.
The $ symbol represents an unbounded upper limit in SVA range expressions.
This is used to express "eventually" semantics without a fixed deadline.
Example: req |-> ##[0:$] ack means "if req, then ack eventually happens."
Caution: unbounded assertions can cause performance issues and may never complete.
In practice, bounded ranges (##[0:100]) are preferred for predictable simulation.
##[1:$] means "at least one cycle, eventually" (not same cycle).`
  },
  {
    id: 67,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Medium",
    question: "Which SVA construct should be used to check that a signal remains stable for N cycles?",
    options: [
      "signal |-> ##N signal",
      "$stable(signal)[*N]",
      "signal throughout ##[1:N] 1'b1",
      "$stable(signal) ##[0:N-1] 1'b1 is invalid"
    ],
    correctAnswer: "B",
    explanation: `$stable(signal)[*N] checks that the signal doesn't change for N consecutive cycles.
[*N] is the repetition operator - it repeats the preceding expression N times.
$stable returns true when a signal's value equals its previous cycle value.
Combining them: $stable(data)[*5] means data is unchanged for 5 consecutive cycles.
Alternative: you could use 'throughout' operator for more complex stability checks.
Example property: @(posedge clk) start |-> $stable(config)[*10];
This is commonly asked in interviews for protocol checks like bus hold times.`
  },
  {
    id: 68,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Hard",
    question: "What is the common pitfall when using $rose or $fell in concurrent assertions?",
    options: [
      "They only work in Verilog, not SystemVerilog",
      "They use sampled values, so glitches between clock edges are invisible",
      "They cannot be used with disable iff",
      "They always cause simulation performance issues"
    ],
    correctAnswer: "B",
    explanation: `$rose, $fell, and $stable operate on sampled (preponed) values at clock edges.
Glitches or transitions that occur between clock edges are not detected.
If a signal goes 0->1->0 between clocks, $rose might not see the pulse.
This is usually correct behavior for synchronous design checks.
But if checking for pulses or async events, immediate assertions may be needed.
Also beware: the "previous" value is from the previous clock edge, not time step.
Interviewers ask this to check understanding of SVA sampling semantics.`
  },
  {
    id: 69,
    type: "mcq",
    topic: "Assertions",
    difficulty: "Hard",
    question: "Why might an assertion pass during simulation but fail in formal verification?",
    options: [
      "Formal tools don't support SVA",
      "Simulation tests limited scenarios, formal explores all possible input combinations including corner cases",
      "Formal verification ignores timing constraints",
      "Assertions are disabled in formal tools"
    ],
    correctAnswer: "B",
    explanation: `Simulation only tests the specific scenarios your testbench generates.
Formal verification exhaustively explores all possible input combinations and states.
An assertion may pass in simulation because your tests never hit the failing corner case.
Formal can find bugs in unreachable states or rare race conditions.
Example: simulation never triggers a specific error injection, but formal finds the path.
This is why combining simulation and formal is best practice in DV.
Formal is especially strong for control logic, protocols, and safety properties.`
  },

  // ==================== COVERAGE QUESTIONS (12 new, IDs 70-81) ====================

  {
    id: 70,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Easy",
    question: "What is the main difference between code coverage and functional coverage?",
    options: [
      "Code coverage is manual, functional coverage is automatic",
      "Code coverage measures lines/branches executed, functional coverage measures verification intent",
      "Functional coverage is only for UVM, code coverage is for Verilog",
      "They are the same thing with different names"
    ],
    correctAnswer: "B",
    explanation: `Code coverage is automatically computed by the simulator and tracks which lines, branches, conditions, and expressions were exercised during simulation.
Functional coverage is user-defined and measures whether specific scenarios, transactions, or corner cases from your verification plan were actually tested.
100% code coverage doesn't mean your design is bug-free - it only means all code ran, not that all behaviors were tested.
Functional coverage answers "did we test what we intended to test?" while code coverage answers "what code got executed?"
In interviews, emphasize that both are needed: code coverage finds dead code, functional coverage ensures completeness.`
  },
  {
    id: 71,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Easy",
    question: "What is a covergroup in SystemVerilog?",
    options: [
      "A group of assertions bundled together",
      "A container for coverpoints and cross coverage definitions",
      "A module that contains only coverage code",
      "A type of testbench component in UVM"
    ],
    correctAnswer: "B",
    explanation: `A covergroup is a user-defined coverage model that encapsulates coverpoints and cross coverage.
It defines WHAT values/scenarios to track and WHEN to sample them (sampling event).
Covergroups can be instantiated multiple times with different sampling conditions.
Example: covergroup cg @(posedge clk); coverpoint opcode; endgroup
Inside a covergroup you define coverpoints (variables to track) and crosses (combinations).
Covergroups are fundamental to functional coverage in SystemVerilog.
They provide the mechanism to translate verification intent into measurable coverage goals.`
  },
  {
    id: 72,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Easy",
    question: "What does a 'bin' represent in functional coverage?",
    options: [
      "A storage location in memory",
      "A bucket that counts how many times a specific value or range was hit",
      "A type of assertion that checks timing",
      "A debug container for waveforms"
    ],
    correctAnswer: "B",
    explanation: `A bin is a counter that tracks how many times a specific value, range, or transition occurred.
Each bin represents a scenario you want to verify was exercised during simulation.
Example: bins low_vals = {[0:15]}; counts hits when value is between 0 and 15.
Bins can be auto-generated or explicitly defined to match your verification intent.
When a bin is "hit" (count > 0), that scenario is considered covered.
Coverage percentage is calculated as (bins hit / total bins) × 100.
Defining meaningful bins is key to writing effective functional coverage.`
  },
  {
    id: 73,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Easy",
    question: "What is the purpose of 'cross coverage'?",
    options: [
      "To check that signals cross zero at the right time",
      "To verify all combinations of two or more coverpoints were exercised",
      "To combine code coverage from multiple simulations",
      "To measure coverage across multiple testbenches"
    ],
    correctAnswer: "B",
    explanation: `Cross coverage tracks combinations of values from multiple coverpoints.
If coverpoint A has 4 bins and coverpoint B has 3 bins, cross creates 4×3=12 combination bins.
Example: cross opcode, data_size; verifies all opcode+size combinations were tested.
This catches cases where each value was tested individually but certain combinations were missed.
Cross coverage is powerful for finding corner cases in protocol testing.
Be careful: crosses can explode combinatorially, so use binsof() to filter relevant combinations.
Interview tip: explain how crosses help find "gaps" in test scenarios.`
  },
  {
    id: 74,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Easy",
    question: "When is a covergroup sampled by default if no sampling event is specified?",
    options: [
      "Every clock cycle automatically",
      "Only when explicitly called with .sample() method",
      "At the end of simulation",
      "Never - it causes a compilation error"
    ],
    correctAnswer: "B",
    explanation: `If no sampling event (@event) is specified in the covergroup definition, sampling is manual.
You must call the .sample() method explicitly to trigger coverage collection.
Example: cg_inst.sample(); - this captures the current values into the covergroup bins.
This gives precise control over when coverage is collected (e.g., only on valid transactions).
Alternatively, specify a sampling event: covergroup cg @(posedge clk); for automatic sampling.
Explicit sampling is often preferred to avoid counting invalid or reset states.
In UVM, coverage is typically sampled in monitors when valid transactions are observed.`
  },
  {
    id: 75,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Medium",
    question: "What is the difference between 'illegal_bins' and 'ignore_bins'?",
    options: [
      "illegal_bins cause errors, ignore_bins are just not counted",
      "They are the same - both exclude values from coverage",
      "ignore_bins cause warnings, illegal_bins cause errors",
      "illegal_bins are for assertions, ignore_bins are for coverage"
    ],
    correctAnswer: "A",
    explanation: `illegal_bins define values that should NEVER occur - hitting them is a verification error.
If an illegal_bin is sampled, the simulator reports an error (design or test bug found).
ignore_bins define values that are valid but not interesting for coverage calculation.
They are excluded from the coverage percentage but don't cause errors when hit.
Example: illegal_bins bad = {4'hF}; - error if value equals 0xF.
Example: ignore_bins skip = {0}; - don't count zero in coverage, but no error if seen.
Use illegal_bins for protocol violations; use ignore_bins for don't-care or reserved values.`
  },
  {
    id: 76,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Medium",
    question: "Why might 100% functional coverage still leave bugs undiscovered?",
    options: [
      "Functional coverage is always incomplete",
      "The coverage model may not capture all important scenarios or corner cases",
      "Simulators have bugs that miss coverage",
      "100% coverage is impossible to achieve"
    ],
    correctAnswer: "B",
    explanation: `Functional coverage only measures what you explicitly defined in your coverage model.
If your model doesn't include certain scenarios, hitting 100% won't guarantee they were tested.
Example: you might cover all opcodes but miss testing back-to-back transactions or error injection.
Coverage is only as good as your verification plan and coverage model design.
This is why coverage closure also involves reviewing the model for completeness.
Combine functional coverage with code coverage, assertions, and formal to increase confidence.
Interview key point: 100% coverage means "we tested everything we planned" not "no bugs remain."`
  },
  {
    id: 77,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Medium",
    question: "What is a 'coverage hole'?",
    options: [
      "A bug in the coverage tool",
      "A bin or scenario that was never hit during simulation",
      "Missing code in the DUT",
      "An assertion that never triggered"
    ],
    correctAnswer: "B",
    explanation: `A coverage hole is a bin that has zero hits - a scenario that was never exercised.
Finding and closing coverage holes is a key part of verification closure.
Holes indicate either: (1) tests don't exercise that scenario, or (2) the scenario is unreachable.
For reachable holes, you need to add directed tests or adjust constraints.
For unreachable holes (impossible scenarios), use ignore_bins to exclude them.
Coverage analysis tools highlight holes to guide test development priorities.
Interview tip: explain your process for analyzing and closing coverage holes systematically.`
  },
  {
    id: 78,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Medium",
    question: "What is 'coverage-driven verification' (CDV)?",
    options: [
      "Writing tests before RTL design",
      "Using coverage metrics to guide test development and determine when verification is complete",
      "Running only directed tests without randomization",
      "Replacing assertions with coverage"
    ],
    correctAnswer: "B",
    explanation: `CDV uses coverage metrics to steer the verification process from start to finish.
First, define coverage goals based on the verification plan (functional coverage model).
Then run tests (often constrained random) and measure coverage progress.
Analyze holes to develop new tests or adjust constraints targeting uncovered scenarios.
Continue until coverage goals are met and all holes are closed or waived.
CDV ensures systematic verification rather than ad-hoc "run tests and hope" approaches.
It provides measurable evidence of verification completeness for signoff.
Key interview point: CDV connects verification plan → coverage model → tests → metrics.`
  },
  {
    id: 79,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Medium",
    question: "What is the advantage of user-defined bins over auto-generated bins?",
    options: [
      "Auto bins are always better because they are automatic",
      "User bins let you focus on important values and ranges matching your verification intent",
      "User bins run faster in simulation",
      "Auto bins don't work with cross coverage"
    ],
    correctAnswer: "B",
    explanation: `Auto bins divide the value range evenly, which may not match what's important to verify.
User-defined bins let you focus on critical values, boundaries, and corner cases.
Example: for a 32-bit address, auto bins create millions of buckets - not useful.
User bins: bins low = {[0:255]}; bins high = {[32'hFFFFFF00:32'hFFFFFFFF]}; - meaningful ranges.
User bins also allow transition coverage: bins seq = (0 => 1 => 2); for sequences.
Auto bins are okay for small enums or when you truly want exhaustive value coverage.
Best practice: define bins that reflect your verification plan's important scenarios.`
  },
  {
    id: 80,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Hard",
    question: "In coverage closure, what should you do with a coverage hole for an unreachable scenario?",
    options: [
      "Keep running more random tests until it's hit",
      "Delete the entire coverpoint",
      "Document it and exclude with ignore_bins or a waiver",
      "Change the RTL to make it reachable"
    ],
    correctAnswer: "C",
    explanation: `Unreachable scenarios are coverage holes that cannot be hit due to design constraints.
Example: certain opcode+mode combinations that are architecturally forbidden.
Running more tests won't help - the scenario is impossible by design.
The correct approach: document why it's unreachable and exclude it from coverage calculation.
Use ignore_bins to exclude, or create a formal waiver with technical justification.
Never modify RTL just to hit coverage - that defeats the purpose of verification.
Interview key: explain your waiver process and how you distinguish unreachable from untested.`
  },
  {
    id: 81,
    type: "mcq",
    topic: "Coverage",
    difficulty: "Hard",
    question: "How can coverage be misleadingly high if sampling occurs during reset?",
    options: [
      "Reset values don't affect coverage",
      "Reset state values may hit bins without testing actual functional scenarios",
      "Coverage tools ignore reset periods automatically",
      "Reset makes all bins illegal"
    ],
    correctAnswer: "B",
    explanation: `If coverage samples during reset, the reset-state values (often 0) may hit bins.
These hits don't represent actual functional testing - they're just initialization values.
Example: sampling 'state' during reset may hit the IDLE bin, inflating coverage.
This gives false confidence - you think IDLE was tested, but only reset was seen.
Solution: guard sampling with valid signals or use iff(!reset) in covergroups.
Example: coverpoint state iff (!reset); - only sample when not in reset.
Interview point: explain how sampling guards ensure coverage reflects real test activity.`
  },

  // ==================== DEBUG QUESTIONS (12 new, IDs 82-93) ====================
  {
    id: 82,
    type: "mcq",
    topic: "Debug",
    difficulty: "Easy",
    question: "A test fails in regression but passes when run standalone. What is the most likely cause?",
    options: [
      "The simulator has a bug",
      "State pollution from a previous test in the regression",
      "The test is flaky and should be deleted",
      "The DUT has a race condition"
    ],
    correctAnswer: "B",
    explanation: `Regression failures that pass standalone are classic symptoms of state pollution.
In regression, tests run sequentially and may share environment state (memory, global variables, static state).
A previous test may leave residual state that affects the failing test's behavior.
Debug approach: check what test runs before the failing one and isolate the sequence.
Solution: ensure proper reset/cleanup between tests, or run with fresh environment per test.
Static variables, persistent memory content, and global UVM resources are common culprits.
Interview tip: describe your systematic approach to bisecting regression-only failures.`
  },
  {
    id: 83,
    type: "mcq",
    topic: "Debug",
    difficulty: "Easy",
    question: "What is the purpose of saving the random seed when a test fails?",
    options: [
      "To make the simulation run faster next time",
      "To reproduce the exact same random sequence and failure scenario",
      "Seeds are not important in verification",
      "To change the test behavior on each run"
    ],
    correctAnswer: "B",
    explanation: `Random seeds control the pseudo-random number generator sequence in constrained-random tests.
Saving the seed allows you to reproduce the exact same stimulus that caused the failure.
Without the seed, the failure might not reproduce, making debugging extremely difficult.
Best practice: always log the seed at test start, and provide a way to re-run with a specific seed.
Command line example: +ntb_random_seed=12345 to replay a specific scenario.
This is fundamental to constrained-random verification methodology.
Interview key point: explain how seed reproducibility enables systematic debug of random failures.`
  },
  {
    id: 84,
    type: "mcq",
    topic: "Debug",
    difficulty: "Easy",
    question: "When debugging, what is the advantage of waveform viewing over log/print messages?",
    options: [
      "Waveforms are always faster to generate",
      "Waveforms show temporal relationships and timing between multiple signals simultaneously",
      "Print statements are never useful",
      "Waveforms don't require any disk space"
    ],
    correctAnswer: "B",
    explanation: `Waveforms excel at showing how multiple signals change relative to each other over time.
You can see signal transitions, timing relationships, and correlate events across the design.
This is critical for debugging timing issues, protocol handshakes, and race conditions.
Print/log debugging shows sequential events but makes temporal correlation difficult.
However, both have their place: logs are great for high-level flow, waveforms for signal-level detail.
Waveforms also let you measure delays, zoom into specific cycles, and trace signal sources.
Interview tip: explain when you'd use each approach and how they complement each other.`
  },
  {
    id: 85,
    type: "mcq",
    topic: "Debug",
    difficulty: "Easy",
    question: "A signal shows 'X' (unknown) in the waveform after reset. What should you check first?",
    options: [
      "The simulator version",
      "Whether all flops and state elements are properly reset",
      "The testbench clock frequency",
      "Delete the signal from the design"
    ],
    correctAnswer: "B",
    explanation: `X-propagation after reset indicates uninitialized state elements.
Check that all flip-flops and memories in the affected path have proper reset connections.
Common causes: missing reset in always_ff, incorrect reset polarity, or reset not reaching all flops.
Trace the X backward in the design to find the source - the first flop outputting X.
Also check for unconnected inputs, tri-state buses without drivers, or uninitialized memories.
X-propagation is a feature, not a bug - it helps catch real hardware initialization issues.
Interview point: explain your systematic X-debug methodology and reset verification approach.`
  },
  {
    id: 86,
    type: "mcq",
    topic: "Debug",
    difficulty: "Medium",
    question: "Your scoreboard reports a mismatch, but the monitor is capturing correct data. Where is the bug most likely?",
    options: [
      "The DUT has a bug",
      "The scoreboard's expected value calculation or comparison logic",
      "The clock is wrong",
      "The testbench should be rewritten from scratch"
    ],
    correctAnswer: "B",
    explanation: `If the monitor captures correct DUT output but scoreboard reports mismatch, the bug is in the scoreboard.
The scoreboard maintains a reference model and compares expected vs actual values.
Common scoreboard bugs: wrong expected value calculation, incorrect ordering assumptions, timing issues.
Debug approach: print both expected and actual values at comparison point, trace expected value origin.
Check if the reference model handles all DUT features (pipelining, reordering, etc.).
Also verify the scoreboard receives transactions in the correct order from multiple monitors.
Interview tip: explain your approach to isolating whether bugs are in DUT, monitor, or scoreboard.`
  },
  {
    id: 87,
    type: "mcq",
    topic: "Debug",
    difficulty: "Medium",
    question: "A test intermittently fails with different seeds. What type of issue does this suggest?",
    options: [
      "A deterministic RTL bug",
      "A race condition or timing-sensitive issue",
      "The test is too short",
      "The coverage model is wrong"
    ],
    correctAnswer: "B",
    explanation: `Intermittent failures with different seeds suggest non-deterministic behavior in the design or testbench.
Race conditions occur when the outcome depends on timing of competing operations.
Different seeds generate different stimulus timing, exposing the race differently each run.
Common causes: clock domain crossings without proper synchronization, shared resource conflicts.
In testbench: race between driver and monitor, or assumption about operation ordering.
Debug approach: look for parallel processes accessing shared state, or missing handshake logic.
Interview key: explain how you isolate intermittent issues and differentiate race from other causes.`
  },
  {
    id: 88,
    type: "mcq",
    topic: "Debug",
    difficulty: "Medium",
    question: "You're debugging a protocol violation. What's the most efficient first step?",
    options: [
      "Rewrite the entire testbench",
      "Check the assertion or checker that fired to understand the exact violation",
      "Increase simulation time",
      "Add more random constraints"
    ],
    correctAnswer: "B",
    explanation: `Assertions and protocol checkers are designed to pinpoint exactly what went wrong and when.
Start by examining the fired assertion: what property was violated, at what time, with what signal values.
This tells you the symptom precisely - much more efficient than hunting blindly.
Next, trace backward in the waveform from the violation time to find the root cause.
The assertion failure time is your anchor point for focused debug.
Well-written assertions include helpful messages indicating expected vs actual behavior.
Interview tip: describe how you leverage assertion failures as starting points for systematic debug.`
  },
  {
    id: 89,
    type: "mcq",
    topic: "Debug",
    difficulty: "Medium",
    question: "A test fails only when run with other tests but the seed is different each run. How do you isolate the issue?",
    options: [
      "Run all tests with the same seed",
      "Bisect the test list to find which preceding test causes the failure",
      "Ignore the failure since seeds differ",
      "Only run standalone tests"
    ],
    correctAnswer: "B",
    explanation: `Bisecting narrows down which preceding test leaves problematic state.
Start by running the failing test after half the regression, then quarter, etc.
This binary search approach quickly identifies the interacting test.
Once found, examine what state that test leaves behind (memories, globals, config).
Common culprits: persistent UVM resource settings, unreset memories, static variables.
Fix: add proper cleanup, or reset more thoroughly between tests.
Interview key: explain your systematic bisection methodology and state isolation techniques.`
  },
  {
    id: 90,
    type: "mcq",
    topic: "Debug",
    difficulty: "Medium",
    question: "The DUT output arrives one cycle later than your scoreboard expects. What type of bug is this?",
    options: [
      "A functional logic error",
      "A latency or pipeline modeling mismatch between DUT and reference model",
      "A syntax error in the testbench",
      "An assertion coverage issue"
    ],
    correctAnswer: "B",
    explanation: `One-cycle-off errors typically indicate latency mismatch between DUT and reference model.
The reference model must accurately reflect the DUT's pipeline depth and timing.
Common causes: reference model missing a pipeline stage, or DUT adding unexpected buffering.
Also check for off-by-one in address calculations or FIFO depth assumptions.
Debug approach: compare DUT and reference model architectures, verify each pipeline stage.
Solution: adjust reference model latency or add synchronization logic in scoreboard.
Interview tip: explain how you maintain reference model accuracy as DUT evolves.`
  },
  {
    id: 91,
    type: "mcq",
    topic: "Debug",
    difficulty: "Medium",
    question: "When debugging reset-related bugs, what's the most important thing to verify?",
    options: [
      "The clock frequency",
      "That all state elements reach known values before normal operation begins",
      "The number of test iterations",
      "The random seed value"
    ],
    correctAnswer: "B",
    explanation: `Reset bugs occur when design doesn't reach a clean, known state before operation.
Verify: all flops reset to defined values, reset propagates to all clock domains, reset timing is correct.
Check reset duration - some designs need multiple cycles for reset to propagate.
For async resets, verify proper synchronization to avoid metastability.
Watch for: flops without reset, incorrect reset polarity, reset release race conditions.
In multi-clock designs, ensure each domain's reset is properly synchronized.
Interview key: describe your reset verification checklist and common reset bug patterns.`
  },
  {
    id: 92,
    type: "mcq",
    topic: "Debug",
    difficulty: "Hard",
    question: "A bug only reproduces in gate-level simulation, not RTL. What should you investigate?",
    options: [
      "The RTL has a hidden bug",
      "Timing issues, X-propagation differences, or RTL/gate mismatch",
      "Gate-level simulation is unreliable",
      "Run RTL simulation longer"
    ],
    correctAnswer: "B",
    explanation: `Gate-level only bugs indicate issues that RTL simulation abstracts away.
Timing issues: gates have delays; paths that worked in zero-delay RTL may fail with real timing.
X-propagation: gate-level is often more pessimistic about X's than RTL simulation.
RTL/gate mismatch: synthesis may have interpreted RTL differently than intended (latch inference, etc.).
Check for: clock domain crossing issues, setup/hold violations, reset timing, uninitialized flops.
Debug approach: compare waveforms at key points between RTL and gate-level runs.
Interview point: explain gate-level debug methodology and common synthesis-vs-RTL surprises.`
  },
  {
    id: 93,
    type: "mcq",
    topic: "Debug",
    difficulty: "Hard",
    question: "An assertion fires at cycle 100, but the root cause occurred 50 cycles earlier. What debug strategy helps?",
    options: [
      "Delete the assertion",
      "Add checkpoints or trace signals backward from the failure to find the originating event",
      "Run simulation for fewer cycles",
      "Change the assertion timing"
    ],
    correctAnswer: "B",
    explanation: `Many bugs manifest long after their root cause due to pipeline depth and state propagation.
Start at the assertion failure (cycle 100) and work backward through the data/control path.
Use waveform analysis to trace which earlier event led to the failing condition.
Add intermediate checkpoints or assertions to narrow down where the problem started.
Hierarchical debug: first identify which major block, then which sub-block, then exact signal.
Consider transaction-level tracing to see which operation at cycle 50 eventually caused the failure.
Interview key: describe your backward-tracing methodology and how you correlate cause to effect.`
  }
];
