# Claude Code: Lean Style Convention Pipeline

**Purpose:** Step-by-step instructions for Claude Code to edit any `.lean` file in this
project to comply with mathlib style conventions (based on `style.md` lines 102+).

**Usage:** When asked to style-fix a Lean file, follow these phases in order. After each
phase, re-read the modified regions to verify correctness. Do NOT change proof logic,
tactic sequences, or mathematical content — only formatting and structure.

**Critical constraint:** Never break compilation. If unsure whether a formatting change
is safe, leave it and flag it with a `-- TODO: style` comment.

---

## Phase 0: Preparation

1. Read the entire target file with the `Read` tool.
2. Note the file length; if over 500 lines, work in sections (0–200, 200–400, etc.).
3. Identify all declaration types present: `def`, `lemma`, `theorem`, `class`,
   `structure`, `inductive`, `instance`, `abbrev`, `example`.
4. Identify all command types present: `variable`, `open`, `section`, `namespace`,
   `notation`, `noncomputable`, `attribute`.

---

## Phase 1: Top-Level Alignment

**Convention:** Every declaration keyword and command keyword must start at column 0.
Content inside `namespace`/`section` blocks is NOT indented.

**Detection:** Use Grep with pattern `^\s+(def |lemma |theorem |class |structure |inductive |instance |variable |open |section |namespace |notation |noncomputable |abbrev )` on the target file.

**Fix:** For each match, remove all leading whitespace from the line so the keyword
starts at column 0.

**Do NOT touch:**
- Lines inside `where` blocks (these are field definitions, not top-level)
- Lines inside `match` or `fun` expressions
- Continuation lines of a declaration (those are handled in Phase 4)

---

## Phase 2: Spacing Around Operators

**Convention:** Spaces on both sides of `:`, `:=`, and all infix operators.

**Detection:** Use Grep with these patterns on the target file:
- Missing space around `:=`: pattern `[^ ]:=|:=[^ \n]`
- Missing space around `:` in type annotations: pattern `[^\s]:[\s]|[\s]:[^\s=]`
  (be cautious — `:` appears in many contexts; only fix type annotation colons)

**Fix:** Insert spaces so `a:b` becomes `a : b` and `x:=y` becomes `x := y`.

**Do NOT touch:**
- Colons inside string literals or comments
- Colons in qualified names (e.g., `Nat.succ`)
- The `::` cons operator
- Colons in `/-! -/` or `/-- -/` delimiters

---

## Phase 3: Operator Placement at Line Breaks

**Convention:** When a line break is needed, place the operator (`:=`, `:`, `→`, `↦`,
`∧`, `∨`, `×`, etc.) at the **end** of the current line, NOT at the beginning of
the next line.

**Detection:** Use Grep with pattern `^\s+(:=|:[^:]|→|↦|∧|∨)` (check context to
avoid false positives on tactic lines or `·` lines).

**Fix:** Move the operator to the end of the preceding line and re-indent the
continuation line appropriately.

**Example — wrong:**
```lean
theorem foo (x : Nat)
    : x = x
    := rfl
```

**Example — correct:**
```lean
theorem foo (x : Nat) :
    x = x :=
  rfl
```

---

## Phase 4: Declaration Indentation

### 4a: Single-line statement → proof body at 2 spaces

**Convention:** When the full declaration statement fits on one line (ending with `:=`
or `:= by`), the proof body on the next line is indented exactly **2 spaces** from
column 0.

**Detection:** Find lines matching `^(theorem|lemma|def|example)\b.*:=\s*(by)?\s*$`,
then check the next non-blank line's indentation.

**Fix:** Adjust leading whitespace of the proof body to exactly 2 spaces.

### 4b: Multi-line statement → continuation at 4 spaces, proof body at 2 spaces

**Convention:** When a declaration statement wraps to multiple lines, continuation
lines are indented **4 spaces** from column 0. The proof body is still at **2 spaces**
(NOT 4+2=6).

**Detection:** Find declarations where the line with the keyword does not contain `:=`.
Check that continuation lines (those before `:=`) start at column 4, and the proof
body (line after `:=` or `:= by`) starts at column 2.

**Fix:**
- Re-indent statement continuation lines to 4 spaces.
- Re-indent proof body to 2 spaces.

**Example — correct:**
```lean
theorem le_induction {P : Nat → Prop} {m}
    (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) :
    ∀ n, m ≤ n → P n := by
  apply Nat.le.rec
  · exact h0
  · exact h1 _
```

---

## Phase 5: `by` Placement

**Convention:** `by` must appear at the **end** of the line preceding the first tactic.
It must never appear on a line by itself. The typical pattern is `:= by`.

**Detection:** Use Grep with pattern `^\s+by\s*$` to find `by` on its own line.

**Fix:** Remove the `by`-only line and append ` by` to the end of the preceding line.
Re-indent the first tactic line if needed (it should be indented 2 spaces from
the declaration keyword, i.e., column 2 for top-level declarations).

**Example — wrong:**
```lean
theorem foo : bar :=
  by
  exact baz
```

**Example — correct:**
```lean
theorem foo : bar := by
  exact baz
```

---

## Phase 6: `have` Statement Formatting

**Convention:** Three patterns depending on justification length:

### 6a: Short justification — same line
```lean
have h1 : n ≠ k := ne_of_lt h
```

### 6b: Long justification — next line, indented +2 from the `have`
```lean
have h1 : n ≠ k :=
  ne_of_lt h
```

### 6c: Tactic justification — `by` always on the same line as `have`
```lean
have h1 : n ≠ k := by apply ne_of_lt; exact h

have h1 : n ≠ k := by
  apply ne_of_lt
  exact h
```

**Detection:**
- Find `have` where `by` appears on the next line: Grep for `have .* :=$` followed
  by a line containing only whitespace + `by`.
- Find `have` split across lines when the justification is short enough for one line.

**Fix:** Move `by` onto the `have` line. Collapse unnecessarily split `have` statements.

---

## Phase 7: Tactic Mode Formatting

### 7a: Focusing dot placement

**Convention:** New subgoals use `·` (focusing dot). The `·` itself is NOT indented
relative to the `by` block, but the tactics after `·` are indented 2 spaces from `·`.

**Example — correct:**
```lean
theorem foo : bar := by
  cases h
  · exact h1
  · apply h2
    exact h3
```

### 7b: One tactic per line

**Convention:** Generally one tactic per line. Exceptions:
- Short tactic sequences closing a goal on one line: `· rw [h]; exact h'`
- Inline tactic proofs: `by tac1; tac2; tac3`

### 7c: `<;>` combinator

**Convention:** Either everything on one line, or the following tactic indented:
```lean
cases x <;>
  simp [a, b, c, d]
```

---

## Phase 8: `calc` Block Formatting

**Convention:**
- `calc` placed at end of preceding line (like `by`), not on its own line.
- Relation symbols (`=`, `≤`, `<`, etc.) aligned across lines.
- Continuation underscores `_` left-justified relative to the first term.

**Detection:** Use Grep for `^\s+calc\s*$` to find `calc` on its own line.

**Fix:** Move `calc` to end of preceding line. Align relation symbols vertically.

**Example — correct:**
```lean
  have : a = c := calc
    a = b := hab
    _ = c := hbc
```

---

## Phase 9: Structure, Class, and Instance Definitions

### 9a: Structure/class fields

**Convention:** Fields indented 2 spaces. Each field should have a docstring.

**Detection:** Find `structure` and `class` declarations. Check field indentation
and presence of `/-- ... -/` above each field.

**Fix:** Re-indent fields to 2 spaces. Add placeholder docstrings if missing:
```lean
  /-- TODO: add docstring -/
  fieldName : Type
```

### 9b: Instances use `where` syntax

**Convention:** Use `where` syntax, not brace-enclosed `{ ... }`.

**Detection:** Use Grep with pattern `instance.*:=\s*\{` or `instance.*:= \{`.

**Fix:** Replace brace-style with `where` syntax. Convert `,` field separators to
newlines.

**Example — wrong:**
```lean
instance : Foo Bar := { field1 := val1, field2 := val2 }
```

**Example — correct:**
```lean
instance : Foo Bar where
  field1 := val1
  field2 := val2
```

---

## Phase 10: Anonymous Function Syntax

**Convention:**
- Use `fun ... ↦ ...` (not `fun ... => ...` and not `λ ... ↦ ...`)
- `λ` is disallowed; always use `fun`
- Use centered dot `·` for simple anonymous functions where possible
- Use `<|` instead of `$`

**Detection:**
- Use Grep with pattern `λ\s` to find disallowed lambda notation.
- Use Grep with pattern `\$\s` to find disallowed `$` operator (check context).
- Note: `fun ... =>` vs `fun ... ↦` — Lean 4 accepts both, but mathlib prefers `↦`.

**Fix:**
- Replace `λ` with `fun`.
- Replace `$` with `<|` in term/tactic contexts.
- Replace `=>` with `↦` in `fun` expressions (NOT in `match` arms — `match` uses `=>`).

**IMPORTANT:** `=>` in `match` arms is correct syntax and must NOT be changed to `↦`.
Only change `=>` to `↦` when it follows `fun`.

---

## Phase 11: Parenthesis Hygiene

**Convention:** Don't orphan parentheses. Closing `)` stays with its arguments.

**Detection:** Use Grep with pattern `^\s*\)+\s*$` to find lines with only closing parens.

**Fix:** Move closing paren to end of the preceding line. Ensure result stays within
100 characters.

---

## Phase 12: Whitespace and Delimiter Rules

### 12a: Space after `←`

**Convention:** In `rw` and `simp` calls, there must be a space after `←`.

**Detection:** Use Grep with pattern `←[^ \]]` (← followed by non-space, non-bracket).

**Fix:** Insert a space after `←`.

### 12b: Space between tactic and arguments

**Convention:** `rw [h]` not `rw[h]`; `simp [h]` not `simp[h]`.

**Detection:** Use Grep with pattern `(rw|simp|erw|simp_rw|norm_num|ring_nf)\[`.

**Fix:** Insert a space before `[`.

### 12c: No empty lines inside declarations

**Convention:** No blank lines within a proof or definition body. Use comments instead.

**Detection:** Look for blank lines between the opening `:=` / `:= by` and the end
of the declaration.

**Fix:** Remove blank lines. If the blank line served as a visual separator, replace
with a short comment like `-- next step` or similar.

### 12d: `<|` instead of `$`

**Convention:** `$` is disallowed in mathlib. Use `<|` for left-pipe.

**Detection:** Grep for `\$` in term/tactic contexts (not inside strings or comments).

**Fix:** Replace `$` with `<|`.

---

## Phase 13: Hypotheses Placement

**Convention:** Prefer arguments left of the colon when the proof begins by introducing
them. Use right-of-colon (∀/→) only for pattern-matching proofs.

**Detection:** Find theorems where the proof starts with `intro` or `fun ... ↦` and
the introduced names correspond to universally quantified variables in the statement.

**Fix:** Move the quantified variables to the left of the colon as explicit arguments.

**Example — wrong:**
```lean
example (n : ℝ) : 1 < n → 0 < n := fun h ↦ by linarith
```

**Example — correct:**
```lean
example (n : ℝ) (h : 1 < n) : 0 < n := by linarith
```

**Exception — pattern matching is fine right-of-colon:**
```lean
lemma zero_le : ∀ n : ℕ, 0 ≤ n
  | 0 => le_rfl
  | n + 1 => ...
```

---

## Phase 14: Line Length

**Convention:** Lines must not exceed 100 characters.

**Detection:** Use Grep with pattern `.{101,}` to find oversized lines.

**Fix:** Break long lines following these rules:
1. For declaration statements: break and indent continuation at 4 spaces.
2. For proof terms: break and indent at 2 additional spaces.
3. For tactic arguments: break after `[` or before long arguments.
4. Place operators before the break, not after.
5. Keep related items together (don't orphan parens).

---

## Phase 15: Binders

**Convention:** Use a space after binders.

**Detection:** Check for `∀x` or `∃x` without a space (pattern `[∀∃][\w]`).

**Fix:** Insert a space: `∀ x`, `∃ y`.

---

## Phase 16: Comments and Documentation Style

**Convention:**
- Module section headers: `/-! ... -/`
- Technical comments (TODO, implementation notes): `/- ... -/`
- Short inline comments: `--`
- Declaration docstrings: `/-- ... -/`
- Multi-line docstrings: do NOT indent subsequent lines

**Detection:** Check for misuse of comment delimiters. Check for indented continuation
lines in `/-- ... -/` docstrings.

**Fix:** Adjust comment delimiter style. Remove leading whitespace from continuation
lines of docstrings.

---

## Execution Summary

When given a file to style-fix, execute these phases:

```
Phase 0:  Read file, understand structure
Phase 1:  Top-level alignment (flush-left keywords)
Phase 2:  Spacing around `:`, `:=`, infix operators
Phase 3:  Operator placement at line breaks
Phase 4:  Declaration indentation (2-space proof, 4-space continuation)
Phase 5:  `by` placement (end of preceding line)
Phase 6:  `have` formatting
Phase 7:  Tactic mode formatting (focusing dots, one-per-line)
Phase 8:  `calc` block formatting
Phase 9:  Structure/class/instance formatting
Phase 10: Anonymous function syntax (`fun`/`↦`/`·`/`<|`)
Phase 11: Parenthesis hygiene
Phase 12: Whitespace and delimiter rules
Phase 13: Hypotheses placement (left of colon)
Phase 14: Line length (≤100 chars)
Phase 15: Binder spacing
Phase 16: Comments and documentation
```

After all phases, re-read the full file and do a final review pass for any
remaining issues. Report a summary of all changes made and write it into a md file called style_fix_{filename}.md
