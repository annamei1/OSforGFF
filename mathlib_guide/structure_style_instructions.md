# How to Fix Declaration Structure & Formatting in a Lean File

Step-by-step instructions for bringing a `.lean` file into compliance with
mathlib style conventions for structuring definitions, theorems, instances,
and related constructs (style.md lines 102-269).

---

## Step 0: Preparation

1. Open the file and enable the 100-character ruler in VS Code.
2. Run `lake build` (or the relevant build command) so you can re-check
   after every batch of edits.
3. Read through the file once to get a sense of the declaration types present
   (`def`, `lemma`, `theorem`, `structure`, `class`, `instance`, `have`, `calc`, etc.).

---

## Step 1: Top-Level Alignment

**Rule:** Every declaration keyword (`def`, `lemma`, `theorem`, `class`,
`structure`, `inductive`, `instance`, ...) and every command keyword
(`variable`, `open`, `section`, `namespace`, `notation`, ...) must start at
column 0, regardless of any enclosing `namespace` or `section`.

**How to check:**
- Search for lines matching `^\s+(def |lemma |theorem |class |structure |instance |variable |open |section |namespace |notation )`.
- Any match indicates an incorrectly indented top-level keyword.

**How to fix:**
- Remove all leading whitespace from these lines.
- Do **not** indent the body of a `namespace` or `section` block.

**Example (wrong):**
```lean
namespace Foo
  theorem bar : ... := ...
end Foo
```
**Example (correct):**
```lean
namespace Foo

theorem bar : ... := ...

end Foo
```

---

## Step 2: Spacing Around Operators

**Rule:** Use spaces on both sides of `:`, `:=`, and all infix operators.

**How to check:**
- Look for `:=` without surrounding spaces (e.g., `foo:=bar`).
- Look for `:` immediately adjacent to a non-space character on either side
  in type annotations (be careful to distinguish from namespace colons).
- Look for infix operators (`+`, `*`, `∧`, `∨`, `→`, `↦`, `≤`, `<`, etc.)
  missing a space on either side.

**How to fix:**
- Insert spaces: `a:b` becomes `a : b`, `x:=y` becomes `x := y`.

---

## Step 3: Operator Placement at Line Breaks

**Rule:** When a line break is needed, place the operator (`:=`, `:`, `→`,
`↦`, `∧`, `∨`, etc.) **before** the line break, not at the beginning of
the next line.

**How to check:**
- Search for lines that begin with `:=`, `:`, `→`, `↦`, or other infix operators.

**Example (wrong):**
```lean
theorem foo (x : Nat)
    : x = x
    := rfl
```
**Example (correct):**
```lean
theorem foo (x : Nat) :
    x = x :=
  rfl
```

---

## Step 4: Single-Line Declaration Indentation (Proof Body = 2 Spaces)

**Rule:** After the theorem statement, the proof body is indented by exactly
**2 spaces** from the declaration keyword.

**How to check:**
- For each `theorem`/`lemma`/`def` that has `:=` at the end of its
  statement, verify the next non-blank line starts at column 2.

**Example (correct):**
```lean
theorem nat_case {P : Nat → Prop} (n : Nat) (H1 : P 0) (H2 : ∀ m, P (succ m)) : P n :=
  Nat.recOn n H1 (fun m IH ↦ H2 m)
```

---

## Step 5: Multi-Line Theorem Statements (Continuation = 4 Spaces)

**Rule:** When a theorem/def statement spans multiple lines, continuation
lines of the **statement** are indented by **4 spaces** from the declaration
keyword. The proof body is still indented by only **2 spaces** (not 4+2=6).

**How to check:**
- Find declarations whose signature wraps. Verify continuation lines
  of the signature start at column 4.
- Verify the proof body still starts at column 2.

**Example (correct):**
```lean
theorem le_induction {P : Nat → Prop} {m}
    (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) :
    ∀ n, m ≤ n → P n := by
  apply Nat.le.rec
  · exact h0
  · exact h1 _
```

**Common mistake:** Indenting the proof by 6 spaces (4 for continuation + 2
for proof). The proof should always be indented 2 from column 0.

---

## Step 6: `by` Placement

**Rule:** `by` is placed at the **end** of the line preceding the first
tactic. It must never appear on a line by itself. The typical pattern is
`:= by` at the end of the theorem statement.

**How to check:**
- Search for lines containing only `by` (possibly with whitespace).
- Search for lines where `by` starts a new line below `:=`.

**How to fix:**
- Move `by` to the end of the previous line, appending it after `:=`.

**Example (wrong):**
```lean
theorem foo : bar :=
  by
  exact baz
```
**Example (correct):**
```lean
theorem foo : bar := by
  exact baz
```

---

## Step 7: Multi-Line Proof Terms (Nested Indentation)

**Rule:** When a proof term takes multiple arguments across lines, each
argument is indented by 2 additional spaces relative to the function it
belongs to. This applies generally whenever a term spans multiple lines.

**How to check:**
- Look for proof terms using `Or.elim`, `And.intro`, `Exists.intro`, etc.
  with arguments on subsequent lines.
- Verify each argument line is indented 2 more spaces than the function call.

**Example (correct):**
```lean
theorem nat_discriminate {B : Prop} {n : Nat} (H1: n = 0 → B) (H2 : ∀ m, n = succ m → B) : B :=
  Or.elim (zero_or_succ n)
    (fun H3 : n = zero ↦ H1 H3)
    (fun H3 : n = succ (pred n) ↦ H2 (pred n) H3)
```

---

## Step 8: Parenthesis Placement

**Rule:** Don't orphan parentheses. Closing `)` should stay with its
arguments, not sit alone on its own line.

**How to check:**
- Search for lines containing only `)` or `))` (with optional whitespace).

**How to fix:**
- Move the closing parenthesis to the end of the preceding line.

---

## Step 9: Short Declarations

**Rule:** Short declarations can and should be written on a single line
when they fit within the 100-character limit.

**How to check:**
- Look for simple one-liner theorems/defs that have been unnecessarily
  split across multiple lines.

**Example (correct):**
```lean
theorem succ_pos : ∀ n : Nat, 0 < succ n := zero_lt_succ

def square (x : Nat) : Nat := x * x
```

---

## Step 10: `have` Statement Formatting

Three patterns depending on length:

### 10a: Short justification — same line
```lean
have h1 : n ≠ k := ne_of_lt h
```

### 10b: Long justification — next line, indented +2
```lean
have h1 : n ≠ k :=
  ne_of_lt h
```

### 10c: Tactic justification — `by` on the same line as `have`
```lean
-- Short tactic proof, one line:
have h1 : n ≠ k := by apply ne_of_lt; exact h

-- Long tactic proof, `by` still on the `have` line:
have h1 : n ≠ k := by
  apply ne_of_lt
  exact h
```

**How to check:**
- Search for `have` statements where `by` appears on the next line
  instead of the same line.
- Search for `have` statements where the justification is short enough
  for one line but has been unnecessarily split.

---

## Step 11: Long Arguments with Line Breaks

**Rule:** When individual arguments within a proof term are long enough to
need their own line breaks, use an additional indent for every continuation
line after the first within that argument.

**How to check:**
- Look for deeply nested proof terms (e.g., using `calc`, `have`, lambdas
  inside function arguments).
- Verify that each level of nesting adds 2 more spaces of indentation.

**Example (correct):**
```lean
theorem Nat.add_right_inj {n m k : Nat} : n + m = n + k → m = k :=
  Nat.recOn n
    (fun H : 0 + m = 0 + k ↦ calc
      m = 0 + m := Eq.symm (zero_add m)
      _ = 0 + k := H
      _ = k     := zero_add _)
    (fun (n : Nat) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k) ↦
      have H2 : succ (n + m) = succ (n + k) := calc
        succ (n + m) = succ n + m   := Eq.symm (succ_add n m)
        _            = succ n + k   := H
        _            = succ (n + k) := succ_add n k
      have H3 : n + m = n + k := succ.inj H2
      IH H3)
```

---

## Step 12: Structure and Class Definitions

**Rule:** Fields in a `structure` or `class` are indented 2 spaces. Every
field must have a docstring (`/-- ... -/`).

**How to check:**
- Find all `structure` and `class` definitions.
- Verify each field line starts at column 2.
- Verify every field is preceded by a `/-- ... -/` docstring.

**How to fix:**
- Re-indent field lines to column 2.
- Add missing docstrings above each field.

**Example (correct):**
```lean
structure PrincipalSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The supremum of the principal segment -/
  top : β
  /-- The image of the order embedding is the set of elements `b` such that `s b top` -/
  down' : ∀ b, s b top ↔ ∃ a, toRelEmbedding a = b
```

**Note:** When the `extends` clause forces a line break, indent the
continuation by 4 spaces:
```lean
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
    DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0
```

---

## Step 13: Constructor Arguments Alignment

**Rule:** When using a constructor that takes several arguments (e.g., `⟨..., ...⟩`),
the arguments should line up.

**Example (correct):**
```lean
theorem Ordinal.sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a ≤ b :=
  ⟨fun h => by simpa only [h, add_zero] using le_add_sub a b,
   fun h => by rwa [← Ordinal.le_zero, sub_le, add_zero]⟩
```

**How to check:**
- Find multi-line anonymous constructor `⟨...⟩` expressions.
- Verify that the second (and subsequent) entries align with the first
  entry after the opening `⟨`.

---

## Step 14: Instance Definitions

**Rule:** Use `where` syntax for instances — avoid enclosing braces `{ }`.

**How to check:**
- Search for `instance` definitions that use `{ ... }` or `:= { ... }`.

**How to fix:**
- Replace brace-style with `where` syntax.

**Example (wrong):**
```lean
instance instOrderBot : OrderBot ℕ := {
  bot := 0,
  bot_le := Nat.zero_le
}
```
**Example (correct):**
```lean
instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_le
```

When inheriting from an existing instance, use `__ :=`:
```lean
instance instOrderBot : OrderBot ℕ where
  __ := instBot
  bot_le := Nat.zero_le
```

---

## Step 15: Hypotheses Left vs. Right of Colon

**Rule:** Prefer placing hypotheses to the **left** of the colon when the
proof begins by introducing them. Use right-of-colon (universal quantifiers /
implications) only when the proof uses pattern matching.

**How to check:**
- Look for theorems that start with `intro` or `fun ... ↦` immediately
  inside the proof.
- If the introduced variables correspond to universally quantified variables
  in the statement, move them to the left of the colon.

**Example (wrong — proof starts by introducing `h`):**
```lean
example (n : ℝ) : 1 < n → 0 < n := fun h ↦ by linarith
```
**Example (correct):**
```lean
example (n : ℝ) (h : 1 < n) : 0 < n := by linarith
```

**Exception — pattern matching is fine right-of-colon:**
```lean
lemma zero_le : ∀ n : ℕ, 0 ≤ n
  | 0 => le_rfl
  | n + 1 => add_nonneg (zero_le n) zero_le_one
```

---

## Summary: Quick-Scan Regex Patterns

Use these to quickly locate violations (adapt for your editor/grep tool):

| Violation | Regex pattern |
|---|---|
| Indented declaration keyword | `^\s+(def\|lemma\|theorem\|class\|structure\|instance\|variable\|open\|section\|namespace) ` |
| Missing space around `:=` | `[^ ]:=\|:=[^ ]` |
| Operator at start of line | `^\s+(:=\|:\|→\|↦)` (false positives possible; check context) |
| `by` on its own line | `^\s+by\s*$` |
| Orphaned closing paren | `^\s*\)+\s*$` |
| Instance with braces | `instance.*:=\s*\{` |
| `λ` instead of `fun` | `λ\s` |
| `$` instead of `<\|` | `\$\s` (in tactic/term context) |
| `fun ... =>` instead of `↦` | `fun.*=>` |
| Missing space after `←` | `←[^ ]` |

---

## Workflow Recommendation

1. **Automated pass:** Run the regex patterns above to find obvious violations.
2. **Declaration-by-declaration pass:** Walk through each `theorem`/`def`/`lemma`
   and check Steps 4-11 (indentation, `by` placement, `have` formatting).
3. **Structure/instance pass:** Check all `structure`, `class`, and `instance`
   definitions for Steps 12-14.
4. **Hypothesis pass:** Review each declaration for Step 15 (left vs. right of colon).
5. **Build and verify:** Run `lake build` to confirm nothing broke.
