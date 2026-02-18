# Style Fix Report: SchwartzTranslationDecay.lean

**File:** `OSforGFF/SchwartzTranslationDecay.lean`
**Date:** 2026-02-18
**Original line count:** 1366

---

## Phase Results

| Phase | Description | Result |
|-------|-------------|--------|
| 0 | Preparation | PASS - File read in sections (1366 lines). Declarations: `def`, `lemma`, `theorem`. Commands: `variable`, `open`, `noncomputable`, `section`. |
| 1 | Top-level alignment | PASS - No indented top-level keywords found. |
| 2 | Spacing around operators | PASS - No missing spaces around `:=` or `:`. |
| 3 | Operator placement at line breaks | PASS - No operators found at start of continuation lines. |
| 4 | Declaration indentation | PASS - Single-line defs have correct 2-space proof body. Multi-line declarations have correct 4-space continuation. |
| 5 | `by` placement | PASS - No `by` on its own line. |
| 6 | `have` formatting | PASS - All `have` statements follow correct patterns (6a/6b/6c). |
| 7 | Tactic mode formatting | PASS - Focusing dots properly placed, one tactic per line. |
| 8 | `calc` block formatting | PASS - No `calc` on its own line. |
| 9 | Structure/class/instance formatting | N/A - No structures, classes, or instances in file. |
| 10 | Anonymous function syntax | **FIX** - Replaced all `fun ... =>` with `fun ... ↦` in code. See details below. |
| 11 | Parenthesis hygiene | PASS - No orphaned closing parentheses. |
| 12 | Whitespace and delimiter rules | PASS - No missing spaces after `←`, no missing spaces before `[`, no `$` usage. |
| 13 | Hypotheses placement | PASS - No obvious candidates for moving quantified variables left of colon. |
| 14 | Line length | **FIX** - Broke 18 lines that exceeded 100 characters. See details below. |
| 15 | Binder spacing | PASS - All binders (`∀`, `∃`) have proper spacing (only `∀ᵐ` found, which is correct). |
| 16 | Comments and documentation | PASS - Module header uses `/-! ... -/`, docstrings use `/-- ... -/`, inline comments use `--`. Multi-line docstring continuation lines are not indented. |

---

## Detailed Changes

### Phase 10: `fun ... =>` to `fun ... ↦`

Replaced all `fun ... =>` with `fun ... ↦` throughout the file (approximately 120+ occurrences). This applies to all anonymous function expressions. The `=>` in `conv` blocks (lines 965, 1347) was correctly preserved as `conv_lhs => arg 2`.

**Key lines affected (representative sample):**
- Line 73: `fun x => K x * ...` -> `fun x ↦ K x * ...`
- Line 77: `fun x => K x * ...` -> `fun x ↦ K x * ...`
- Line 82: `K = fun x => ...` -> `K = fun x ↦ ...`
- Line 107: `fun x hx => hx` -> `fun x hx ↦ hx`
- Line 215: `fun m n hmn =>` -> `fun m n hmn ↦`
- Line 217: `fun n =>` -> `fun n ↦`
- Lines 251, 266, 313, 334, 408, 437, 441, 454, 457, 461-464, 470-473, 478, 500, 502-503, 505, 510, 513, 515, 517, 536-538, 578, 603, 608, 632, 676, 680, 683, 696, 705, 738, 782-783, 786, 788, 806, 839, 864, 888, 890, 893, 911, 942, 944, 954-955, 957, 967, 970-972, 975, 978, 987, 990, 998, 1025, 1031, 1035, 1082-1083, 1131, 1146, 1155, 1160, 1171, 1184, 1205, 1235, 1242, 1246, 1248-1251, 1260, 1266, 1268, 1270, 1288, 1291-1292, 1295, 1301, 1304, 1306, 1308, 1323-1325, 1346, 1354 (and more)

### Phase 14: Line Length Fixes

Broke the following lines that exceeded 100 characters:

1. **Line 116** (was 113 chars): Split `le_trans hbound (div_nonpos_of_nonpos_of_nonneg ...)` across 3 lines.
2. **Line 135** (was 101 chars): Split `rw [indicator_of_notMem ..., mul_zero, norm_zero]` across 2 lines after the first argument.
3. **Lines 303, 770** (were 106 chars each): Split `have hxy_bound ... := by simpa ...` by moving `simpa` to next line (2 occurrences).
4. **Lines 352, 805** (were 101 chars each): Split `refine setIntegral_mono_on ...` across 2 lines (2 occurrences).
5. **Line 442** (was 102 chars): Split `have h_sing_int : Integrable (Function.uncurry ...)` by moving `Integrable` to continuation line.
6. **Line 491** (was 101 chars): Split `.complex_ofReal.aestronglyMeasurable` to continuation line.
7. **Line 507** (was 103 chars): Split `have h_tail_int : Integrable (Function.uncurry ...)` by moving `Integrable` to continuation line.
8. **Line 513** (was 105 chars): Split `have h_dom : Integrable (fun ...)` by moving `Integrable` to continuation line.
9. **Line 612** (was 104 chars): Split `have h_fKsing_vanish :` onto its own line with type on continuation.
10. **Line 715** (was 104 chars): Split `have h_fKtail_vanish :` onto its own line with type on continuation.
11. **Line 798** (was 101 chars): Split `h1.comp (measurable_id.sub measurable_const)` to next line.
12. **Line 837** (was 103 chars): Split `(integral_add_compl hs_meas h_int).symm` to next line.
13. **Line 908** (was 107 chars): Split `h1.comp (measurable_id.sub measurable_const)` to next line.
14. **Line 923** (was 104 chars): Split long comment across 2 lines.
15. **Line 1131** (was 101 chars): Split `hK_cont.continuousAt (...)` across 2 lines.
16. **Line 1148** (was 148 chars): Split long `have h_eq` type across 3 lines.
17. **Line 1231** (was 101 chars): Split `obtain` across 2 lines.
18. **Line 1315** (was 105 chars): Split `have h_dom` type across 3 lines.
19. **Line 1336** (was 107 chars): Split `have h1` type across 3 lines.
20. **Line 1231** (was 113 chars): Split long comment across 2 lines.

---

## Items Flagged for Manual Review

None. All changes are purely formatting (arrow syntax and line breaks). No proof logic was modified.

---

## Summary

- **Total phases executed:** 17 (Phases 0-16)
- **Phases with fixes:** 2 (Phase 10, Phase 14)
- **Phases passed:** 14
- **Phases N/A:** 1 (Phase 9)
- **Changes made:** ~120+ `=>` to `↦` replacements, ~20 line-length fixes
