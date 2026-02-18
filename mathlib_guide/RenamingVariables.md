## L2TimeIntegral.lean

### Rules applied

1. **Types with mathematical content use uppercase letters** (style.md lines 22-26)
   - Measure spaces: `X`, `Ω` (not lowercase `α`)
   - Normed spaces: `E` (not lowercase `β`)
   - The old convention of using Greek letters for all types is deprecated
2. **Generic type variables use `α`, `β`, `γ`, ...** (style.md line 12) - only for truly generic types without mathematical structure
3. **Elements of a generic type use `x`, `y`, `z`, ...** (style.md line 14)

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `variable` declaration (line 558) | `α` | `X` | 1 | Type with `MeasurableSpace` structure should use uppercase letter |
| All function signatures in Minkowski section (lines 560-665) | `α` | `X` | 1 | Functions taking `α → ℝ` updated to `X → ℝ` for consistency with variable declaration |
| `memLp_two_lintegral_nnnorm_sq` (line 860) | `α` | `X` | 1 | Type with `MeasurableSpace` structure should use uppercase |
| `memLp_two_lintegral_nnnorm_sq` (line 860) | `β` | `E` | 1 | Type with `NormedAddCommGroup` structure should use uppercase (E is standard for normed spaces) |
| `minkowski_weighted_L2_sum_proved` (lines 665-694) | `ω` | `x` | 3 | Element of generic type (with `MeasurableSpace` instance only) should use `x`, `y`, `z`, ...; `ω` is reserved for elements of a concrete probability space `Ω` |

### Notes

- **Key principle applied**: Types with mathematical content should use uppercase letters (style.md lines 22-26). The old convention of using lowercase Greek letters (`α`, `β`, `γ`) for all types is deprecated.
  - `MeasurableSpace` structure → Use `X` or `Ω` (uppercase)
  - `NormedAddCommGroup` structure → Use `E` (standard for normed spaces) or `G` (for groups)
- The file was inconsistent: it used `Ω` for measure spaces in most places (lines 57, 715, 874) but used lowercase `α` in the Minkowski section (line 558) and in `memLp_two_lintegral_nnnorm_sq` (line 860).
- `ω` is correctly used throughout the non-Minkowski sections of the file, where it denotes an element of `Ω` (a concrete measure/probability space with mathematical meaning).
- In the Minkowski section, elements of the measure space type follow the generic element convention `x`, `y`, `z`, not the probabilistic convention `ω`.
- No other violations were found. Variables like `f`, `g` (functions), `s`, `u` (real-valued integration variables), `n` (natural numbers), `h`/`h_*` (hypotheses), and `μ` (measures) all comply with the stated conventions.

## SchwartzTranslationDecay.lean

### Rules applied

1. **Sets use `s`, `t`, ...** (style.md line 18)
   - Set variables `K`, `S`, `L` renamed to `s`, `t`, `t₁` respectively
2. **Natural numbers use `m`, `n`, `k`, ...** (style.md line 19)
   - Natural number variable `N` renamed to `n`

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `bounded_of_continuous_tendsto_zero` | `K : Set E` | `s` | 1 | Set variable must use `s`, `t`, ... |
| `bounded_of_continuous_tendsto_zero` | `S` (filter set) | `t` | 1 | Set variable must use `s`, `t`, ... |
| `bounded_of_continuous_tendsto_zero` | `hK_cpct`, `hK` | `hs_cpct`, `hs` | 1 | Hypothesis names follow renamed set |
| `bounded_of_continuous_tendsto_zero` | `hS_mem`, `hS` | `ht_mem`, `ht` | 1 | Hypothesis names follow renamed set |
| `bounded_of_continuous_tendsto_zero` | `hK_sub` | `hs_sub` | 1 | Hypothesis names follow renamed set |
| `integrable_tail_small` (statement) | `∃ K : Set E` | `∃ s : Set E` | 1 | Set variable in existential must use `s`, `t`, ... |
| `integrable_tail_small` | `N : ℕ` | `n` | 2 | Natural number must use `m`, `n`, `k`, ... |
| `integrable_tail_small` | `hN` | `hn` | 2 | Hypothesis name follows renamed variable |
| `convolution_vanishes_of_integrable_and_C0` | `K : Set E` | `s` | 1 | Set variable must use `s`, `t`, ... |
| `convolution_vanishes_of_integrable_and_C0` | `S` (filter set) | `t` | 1 | Set variable must use `s`, `t`, ... |
| `convolution_vanishes_of_integrable_and_C0` | `L` (compact set) | `t₁` | 1 | Set variable must use `s`, `t`, ... (subscript to avoid collision) |
| `convolution_vanishes_of_integrable_and_C0` | `R_K`, `R_L` | `R_s`, `R_t₁` | 1 | Derived radius names follow renamed sets |
| `convolution_vanishes_of_integrable_and_C0` | `hK_cpct`, `hK_meas`, `hK_bound`, `hKc_bound` | `hs_cpct`, `hs_meas`, `hs_bound`, `hsc_bound` | 1 | Hypothesis names follow renamed set |
| `convolution_vanishes_of_integrable_and_C0` | `hL_cpct`, `hL_sub`, `hR_L` | `ht₁_cpct`, `ht₁_sub`, `hR_t₁` | 1 | Hypothesis names follow renamed set |
| `convolution_vanishes_of_integrable_and_C0` | `hS_mem`, `hS` | `ht_mem`, `ht` | 1 | Hypothesis names follow renamed set |
| `convolution_vanishes_of_integrable_and_C0` | `hxK`, `hg_small_on_K` | `hxs`, `hg_small_on_s` | 1 | Member/predicate names follow renamed set |
| `schwartz_bilinear_translation_decay_proof` Step 7 | `S`, `L` | `t`, `t₁` | 1 | Set variables must use `s`, `t`, ... |
| `schwartz_bilinear_translation_decay_proof` Step 7 | `R_L`, `hR_L`, `hL_cpct`, `hL_sub`, `hS_mem`, `hS` | `R_t₁`, `hR_t₁`, `ht₁_cpct`, `ht₁_sub`, `ht_mem`, `ht` | 1 | Hypothesis names follow renamed sets |
| `schwartz_bilinear_translation_decay_proof` Step 8 | `K : Set E`, `S`, `L` | `s`, `t`, `t₁` | 1 | Set variables must use `s`, `t`, ... |
| `schwartz_bilinear_translation_decay_proof` Step 8 | `hK_cpct`, `hK_meas`, `hK_bound`, `hKc_bound`, `hKt_small_on_K` | `hs_cpct`, `hs_meas`, `hs_bound`, `hsc_bound`, `hKt_small_on_s` | 1 | Hypothesis names follow renamed set |
| `schwartz_bilinear_translation_decay_proof` Step 8 | `R_K`, `R_L`, `hR_K`, `hR_L` | `R_s`, `R_t₁`, `hR_s`, `hR_t₁` | 1 | Derived names follow renamed sets |
| `schwartz_bilinear_translation_decay_proof` Step 8 | `hS_mem`, `hS`, `hL_cpct`, `hL_sub` | `ht_mem`, `ht`, `ht₁_cpct`, `ht₁_sub` | 1 | Hypothesis names follow renamed sets |
| `h_neg_cocompact` proof | `S`, `K` | `t`, `s` | 1 | Set variables must use `s`, `t`, ... |
| `h_neg_cocompact` proof | `hS`, `hK_cpct`, `hK_sub` | `ht`, `hs_cpct`, `hs_sub` | 1 | Hypothesis names follow renamed sets |

### Notes

- **Upper case `K` for the kernel function** (`K : E → ℝ`) is correct — it represents a mathematical kernel with conventional upper case notation (style.md lines 22-24).
- **Upper case `M`, `B`, `C`** for bound constants are correct — these are conventional mathematical notation for bounds/constants.
- **`R₀`, `R`** for radii are correct — conventional mathematical notation.
- **Greek letters `ε`, `η`, `δ`** for small quantities are correct — standard mathematical convention.
- **`If`, `I_Ksing`** for integral quantities are not ideal per strict rules (elements of ℝ should be `x`, `y`, `z`), but they are let-bindings for computed values with clear mathematical meaning and renaming them would reduce readability. They were left unchanged.
- The `hK_meas` shadowing issue in Step 8 (where a local `hK_meas : MeasurableSet K` shadowed the outer `hK_meas : Measurable K`) was resolved by renaming the local one to `hs_meas : MeasurableSet s`.

## QuantitativeDecay.lean

### Rules applied

1. **Generic type variables use `α`, `β`, `γ`, ...** (style.md line 12) — `α` is reserved for generic types, not for real-valued parameters
2. **Natural numbers use `m`, `n`, `k`, ...** (style.md line 19) — natural number parameters should use lowercase `m`, `n`, `k`
3. **Sets use `s`, `t`, ...** (style.md line 18) — set variables should use `s`, `t`

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `exp_decay_implies_polynomial_decay` | `α : ℝ` | `p` | 1 | `α` is reserved for generic types; `p` is conventional for real exponents in Mathlib analysis |
| `exp_decay_implies_polynomial_decay` | `hα` | `hp` | 1 | Hypothesis name follows renamed variable |
| `norm_exp_decay_implies_polynomial_decay` | `α : ℝ` | `p` | 1 | `α` is reserved for generic types |
| `norm_exp_decay_implies_polynomial_decay` | `hα` | `hp` | 1 | Hypothesis name follows renamed variable |
| `convolution_polynomial_decay` | `A : Set E` | `s` | 3 | Set variable must use `s`, `t`, ... |
| `convolution_polynomial_decay` | `hA_meas` | `hs_meas` | 3 | Hypothesis name follows renamed set |
| `convolution_polynomial_decay` | `hA_bound` | `hs_bound` | 3 | Hypothesis name follows renamed set |
| `convolution_polynomial_decay` | `hAc_bound` | `hsc_bound` | 3 | Hypothesis name follows renamed set complement |
| `convolution_polynomial_decay` | `c_A` | `c_s` | 3 | Derived constant name follows renamed set |
| `convolution_polynomial_decay` | `hc_A_pos` | `hc_s_pos` | 3 | Hypothesis name follows renamed constant |
| `convolution_polynomial_decay` | `c_Ac` | `c_sc` | 3 | Derived constant name follows renamed set complement |
| `convolution_polynomial_decay` | `hc_Ac_pos` | `hc_sc_pos` | 3 | Hypothesis name follows renamed constant |
| `convolution_compactSupport_decay` | `N : ℕ` | `n` | 2 | Natural number must use `m`, `n`, `k`, ... |
| `convolution_compactSupport_decay` | `_hN` | `_hn` | 2 | Hypothesis name follows renamed variable |
| `schwartz_bilinear_translation_decay_polynomial_proof` | `α : ℝ` | `p` | 1 | `α` is reserved for generic types |
| `schwartz_bilinear_translation_decay_polynomial_proof` | `hα` | `hp` | 1 | Hypothesis name follows renamed variable |
| `schwartz_bilinear_translation_decay_polynomial_proof` | `hN_gt_α` | `hN_gt_p` | 1 | Hypothesis name follows renamed variable |

### Notes

- **`m : ℝ` for mass parameter** was not renamed despite the convention that `m` is for natural numbers (style.md line 19). The variable `m` represents a physical mass/rate parameter, and `m` for mass is universally standard mathematical notation in the physics context of this file (Reed-Simon, Glimm-Jaffe). Per lines 22-24, standard mathematical notation takes precedence.
- **`N` as a local `let` binding** in the main theorem (`let N := max p d + 1`) was not renamed because it is a real number (not a natural number), so the `m`, `n`, `k` convention does not apply. The uppercase is conventional for a "large parameter" in analysis.
- **`r : ℝ` for decay rate** in `PolynomialDecayBound` and `one_add_half_pow_le` was not renamed. While `r` is listed under "predicates and relations," it is used here as a conventional real-valued rate/exponent parameter. No convention letter exists specifically for arbitrary reals, and `r` for "rate" is unambiguous in context.
- **`I_u`, `I_v`, `I_Ksing`** (integral norms), **`C_u`, `C_v`, `C_f`, `C_K`** (bound constants), and **`K_sing`, `K_tail`, `K_refl`** (kernel decomposition parts) are compound descriptive names that fall outside the single-letter conventions.
- **`M`** for bound constants was not renamed — uppercase `M` for a supremum bound is standard mathematical convention.
- All docstrings and comments referencing renamed variables were updated for consistency.