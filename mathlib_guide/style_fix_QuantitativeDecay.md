# Style Fix Report: QuantitativeDecay.lean

**File:** `OSforGFF/QuantitativeDecay.lean`
**Date:** 2026-02-18
**Total lines:** ~1060

---

## Phase Results

| Phase | Description | Result |
|-------|-------------|--------|
| 0 | Preparation | PASS - File read in sections (1060 lines). Declarations: `structure`, `def`, `lemma`, `theorem`. Commands: `open`, `noncomputable`, `section`, `variable`. |
| 1 | Top-level alignment | PASS - All declaration and command keywords already at column 0. |
| 2 | Spacing around operators | PASS - No missing spaces around `:=` or `:`. |
| 3 | Operator placement at line breaks | PASS - No operators found at start of continuation lines. |
| 4 | Declaration indentation | PASS - All multi-line declarations use 4-space continuation and 2-space proof body. |
| 5 | `by` placement | PASS - No `by` found on its own line. |
| 6 | `have` formatting | PASS - All `have` statements properly formatted. |
| 7 | Tactic mode formatting | PASS - Focusing dots and tactic indentation correct. |
| 8 | `calc` block formatting | PASS - No `calc` on its own line. |
| 9 | Structure/class/instance | N/A - One `structure` present; fields lack docstrings (see manual review). No instances. |
| 10 | Anonymous function syntax | **FIX** - Changed all `fun ... =>` to `fun ... ↦` (56 occurrences). No `λ` or `$` found. |
| 11 | Parenthesis hygiene | PASS - No orphaned closing parentheses. |
| 12 | Whitespace and delimiter rules | **FIX** - Removed 1 blank line immediately after `:= by` in main theorem (line 771). No `←` spacing issues. No missing tactic-bracket spaces. No `$` usage. |
| 13 | Hypotheses placement | PASS - No obvious cases where intro'd variables should move left of colon (proofs are complex tactic proofs, not simple intro patterns). |
| 14 | Line length | **FIX** - Broke 4 lines exceeding 100 characters (original lines 340, 946, 982, 1002). |
| 15 | Binder spacing | PASS - One false positive (`∀ᵐ` on line 988 is special notation, not a regular binder). |
| 16 | Comments and documentation | **FIX** - Removed leading whitespace from continuation lines in 6 multi-line docstrings. |

---

## Changes Made

### Phase 10: Anonymous function syntax (`fun =>` to `fun ↦`)

56 occurrences of `fun ... =>` changed to `fun ... ↦` throughout the file. Key locations:

- Line 76: `fun m => SchwartzMap.seminorm` -> `fun m ↦ SchwartzMap.seminorm`
- Line 87: `fun _ : Fin 0 => E` -> `fun _ : Fin 0 ↦ E`
- Line 107: `fun x => ?_` -> `fun x ↦ ?_`
- Line 281: `fun x => ∫ y, ...` -> `fun x ↦ ∫ y, ...`
- Lines 287-288: `fun _ => norm_nonneg _` -> `fun _ ↦ norm_nonneg _`
- Line 304: `fun y => v (x - y)` -> `fun y ↦ v (x - y)`
- Line 306: `fun y => u y * v (x - y)` -> `fun y ↦ u y * v (x - y)`
- Lines 319-320: `fun y => ‖...‖` -> `fun y ↦ ‖...‖`
- Line 345: `fun _ => norm_nonneg _` -> `fun _ ↦ norm_nonneg _`
- Line 349: `fun y => ‖v y‖` -> `fun y ↦ ‖v y‖`
- Line 394: `fun _ => norm_nonneg _` -> `fun _ ↦ norm_nonneg _`
- Line 443: `fun y => ∫ x, f x * ...` -> `fun y ↦ ∫ x, f x * ...`
- Lines 455-456: `fun x =>` and `fun _ => (1 : ℝ)` -> `fun x ↦` and `fun _ ↦ (1 : ℝ)`
- Line 465: `fun _ => abs_nonneg _` -> `fun _ ↦ abs_nonneg _`
- Line 519: `fun x => |kernelSingular ...|` -> `fun x ↦ |kernelSingular ...|`
- Lines 536, 540, 551, 553, 561, 578: various `fun x =>` -> `fun x ↦`
- Line 600: `fun z => |kernelSingular ...|` -> `fun z ↦ |kernelSingular ...|`
- Line 623: `fun y => ∫ x, ...` -> `fun y ↦ ∫ x, ...`
- Lines 629, 632, 654: kernel tail decay functions
- Line 664: `fun z => (kernelTail ...)` -> `fun z ↦ (kernelTail ...)`
- Lines 686, 711, 715: integrability helpers
- Lines 859, 862: H definition and bound
- Lines 880, 892, 900-903, 908-914: kernel integrability proofs
- Lines 964, 966, 975, 977, 982-983: final assembly
- Line 1040: `fun x => by ring` -> `fun x ↦ by ring`

**NOT changed:** `conv_lhs =>` on line 1045 (correct conv tactic syntax, not a `fun` expression).

### Phase 12: Blank line removal

- Removed blank line at original line 771 (between `:= by` and first tactic of main theorem proof).

### Phase 14: Line length (> 100 characters)

1. **Original line 340** (117 chars): Broke `exact Real.rpow_le_rpow (by positivity) (by linarith) (lt_of_le_of_lt ...)` across two lines.
2. **Original line 946** (124 chars): Broke the `have hint_sum` type annotation across three lines.
3. **Original line 982** (109 chars): Split when converting `fun (y : E) (x : E) => ...` to `fun (y : E) (x : E) ↦ ...` by moving the `Function.uncurry` argument to its own line.
4. **Original line 1002** (103 chars): Broke `have h_conv_decay := convolution_polynomial_decay ...` onto two lines.

### Phase 16: Docstring indentation

Removed leading whitespace from continuation lines in 6 docstrings:

1. **Line 56-57**: `PolynomialDecayBound` structure docstring - removed 4-space indent from line 57.
2. **Lines 64-69**: `schwartz_has_polynomial_decay` docstring - removed 2-space indent from formula on line 67.
3. **Lines 118-121**: `exp_decay_implies_polynomial_decay` docstring - removed 4-space indent from line 119.
4. **Lines 270-275**: `convolution_polynomial_decay` docstring - removed 4-space indent from lines 271-275.
5. **Lines 439-440**: `convolution_compactSupport_decay` docstring - removed 4-space indent from line 440.
6. **Lines 616-617**: `convolution_expDecay_polynomial_decay` docstring - removed 4-space indent from line 617.
7. **Lines 746-758**: Main theorem docstring - removed 2-space indent from formula on line 752.

---

## Items Flagged for Manual Review

1. **Phase 9a - Structure field docstrings**: The `PolynomialDecayBound` structure (line 58) has three fields (`C`, `hC_pos`, `bound`) without individual docstrings. Mathlib convention requires `/-- TODO: add docstring -/` above each field. Not added per the constraint to not add docstrings to unchanged code.

2. **Phase 12c - Blank lines in proof bodies**: Several blank lines exist within long proof bodies throughout the file (particularly in `convolution_polynomial_decay`, `convolution_compactSupport_decay`, `convolution_expDecay_polynomial_decay`, and the main theorem). Only the most clear-cut case (blank line immediately after `:= by`) was removed. The remaining blank lines serve as visual separators in very long proofs (300+ lines) and their removal would significantly reduce readability. Manual judgment is needed to determine if these should be replaced with comments.

3. **Phase 13 - Hypotheses placement**: No changes made. The proofs are complex multi-step tactic proofs, not simple `intro`/`fun ↦` patterns that would benefit from moving hypotheses left of the colon.
