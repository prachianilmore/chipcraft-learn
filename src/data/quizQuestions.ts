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
  }
];
