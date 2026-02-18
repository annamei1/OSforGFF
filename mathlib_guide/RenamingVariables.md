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

## FrobeniusPositivity.lean

### Rules applied

No violations found. All variable binders comply with the naming conventions in style.md lines 9-24.


## SchurProduct.lean

### Rules applied

No violations found. All variable binders comply with the naming conventions in style.md lines 9-24.


## FunctionalAnalysis.lean

### Rules applied

1. **Subscript convention** — Indexed variables use Unicode subscripts (`f₁`, `f₂`) rather than ASCII digits (`f1`, `f2`)
2. **Natural numbers use `m`, `n`, `k`, ...** (style.md line 19) — uppercase `N` is reserved for types, not natural number values
3. **Measures use `μ`, `ν`, ...** — standard Greek letter convention; `d`-prefix (`dμ_real`) is non-standard
4. **Real-valued constants use concise mathematical names** (`M`, `B`, `C`) — snake_case descriptive names (`Cf`, `total_C`, `C_deriv`) are non-idiomatic
5. **Sets use `s`, `t`, ...** (style.md line 18) — snake_case set names (`K_t`, `K_v`) are non-idiomatic

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `linfty_mul_L2_CLM` `map_add'` | `f1`, `f2` | `f₁`, `f₂` | 1 | Indexed variables must use Unicode subscripts |
| `liftMeasure_real_to_complex` | `dμ_real` | `ν` | 3 | Measures use Greek letters `μ`, `ν`; `d`-prefix is non-standard |
| `liftMeasure_real_to_complex` | `dμ_complex_measure` | `ν'` | 3 | Derived measure from `ν`; long snake_case is non-idiomatic |
| `schwartz_bilinear_integrable_of_translationInvariant_L1` | `Cf` | `M` | 4 | Real-valued bound constant uses concise math name |
| `schwartz_bilinear_integrable_of_translationInvariant_L1` | `hCf` | `hM` | 4 | Hypothesis name follows renamed variable |
| `schwartz_integrable_decay` | `N : ℕ` | `m` | 2 | Natural numbers use `m`, `n`, `k` |
| `schwartz_integrable_decay` | `_hN` | `_hm` | 2 | Hypothesis name follows renamed variable |
| `schwartz_integrable_decay` | `total_C` | `B` | 4 | Real-valued bound uses concise math name |
| `schwartz_vanishing_linear_bound_general` | `C_deriv` | `M` | 4 | Real-valued bound uses concise math name |
| `double_mollifier_convergence` (integrability proof) | `K_t` | `s₁` | 5 | Set variable uses `s`, `t` convention |
| `double_mollifier_convergence` (integrability proof) | `K_v` | `s₂` | 5 | Set variable uses `s`, `t` convention |

### Notes

- **`n : ℕ`** (section variable, line 124) is compliant — follows `m`, `n`, `k` convention for natural numbers.
- **`𝕜 : Type`** (line 136) is compliant — standard notation for fields.
- **`E : Type`**, **`V : Type*`**, **`F : Type*`** are compliant — uppercase for types with mathematical content (vector spaces).
- **`α : Type*`** (line 149) is compliant — generic type variable.
- **`μ : Measure α`** is compliant — standard Greek letter for measures.
- **`φ`** for bump functions, **`ψ`** for mollifiers, **`θ`** for angles are all standard mathematical notation.
- **`ρ`, `σ`, `δ`** for real parameters (radius, decay rate, small quantity) are standard mathematical notation.
- **`K₀`** for a kernel function is compliant — uppercase with subscript for named mathematical objects.
- **`K : Set ...`** (compact sets in `integrableOn_compact_diff_ball`) was not renamed — uppercase `K` for compact sets is standard mathematical notation (style.md lines 22-24).
- **`M`** in `integrableOn_compact_diff_ball` (line 461) was not renamed — already compliant as a concise bound constant.
- **`A`, `B`** (points in MVT argument, `schwartz_vanishing_linear_bound_general`) were not renamed — uppercase for named geometric points is conventional.
- **`C_k`** in the existential `∃ C_k > 0` (line 879) was not renamed — it is immediately consumed by `choose` and does not persist as a named binding.
- **`bound`** (line 595) was not renamed — it is a descriptive let-binding for a dominating function within a proof, not a mathematical constant.
- **`F`** (line 1158) for a function in a proof was not renamed — uppercase is acceptable for named functions in mathematical arguments.
- Docstrings referencing renamed variables (`N` → `m` in `schwartz_integrable_decay`) were updated for consistency.

## PositiveDefinite.lean

### Rules applied

1. **Types with mathematical content use uppercase letters** (style.md lines 22-24)
   - Groups: `G` (not lowercase `α`)

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `IsPositiveDefinite` (line 36) | `α` | `G` | 1 | Type with `AddGroup` structure should use uppercase; `G` is the conventional letter for groups |
| `IsPositiveDefinite` (line 37) | `α` (in `Fin m → α`) | `G` | 1 | Consistent with type parameter rename |
| Docstrings (lines 19, 31) | `α` | `G` | 1 | Updated to match renamed type parameter |

### Notes

- **`E`, `H`** (in `isPositiveDefinite_precomp_linear`) are compliant — uppercase for types with `AddCommGroup`/`Module` structure (vector spaces).
- **`ψ`** for the positive definite function is compliant — standard mathematical notation for functions.
- **`φ`** for the positive definite function in `IsPositiveDefinite` is compliant — standard mathematical notation.
- **`T`** for the linear map is compliant — uppercase for linear operators is standard mathematical notation.
- **`hPD`** for the positive definiteness hypothesis is compliant — `h`-prefix convention.
- **`m : ℕ`** is compliant — follows `m`, `n`, `k` convention for natural numbers.
- **`x`** for elements is compliant — follows `x`, `y`, `z` convention.
- **`ξ`** for complex coefficients is compliant — standard mathematical notation for coefficients in Fourier/harmonic analysis.
- **`v`** in `fun v : E =>` is compliant — conventional mathematical notation for elements of a vector space.
- **`i`, `j`** for sum indices are compliant — standard index variables.
- Since `G` is an implicit parameter (`{G : Type*}`), no changes were needed in calling files (`GaussianRBF.lean`, `Minlos.lean`, `MinlosAnalytic.lean`, `GFFMconstruct.lean`) — Lean infers the type automatically.

## HadamardExp.lean

### Rules applied

1. **Assumptions use `h`, `h₁`, ...; unused binders use `_`** (style.md line 15) — proof terms serving as assumptions should use the `h` prefix, and unused binders should be anonymous (`_`)

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `summable_hadamardQuadSeries` (line 278) | `a` | `_` | 1 | Unused membership proof (`i ∈ Finset.univ`) in `fun i a => h_inner i`; `a` is never referenced, so it should be `_` |

### Notes

- **Matrices** (`A`) correctly use uppercase per the mathematical content convention (style.md lines 22-24).
- **`ι`** for the finite index type is standard Mathlib notation — compliant.
- **`u`** for universe is compliant (style.md line 11).
- **`x`** for vectors (`ι → ℝ`) and `x` as a local real scalar (`set x : ℝ := A i j`) are compliant — elements of a generic type (style.md line 14).
- **`i`, `j`** for index variables over `ι` are compliant.
- **`n`, `k`** for natural numbers are compliant (style.md line 19).
- **`ε`** for perturbation parameters is standard mathematical notation — compliant.
- **`f`** for the sequence `ℕ → ℝ` in the quadratic form proof is conventional mathematical notation for functions — compliant.
- **`fC`, `fR`** (complex and real series terms) are compound descriptive let-bindings within a proof — not single-letter convention variables.
- **`s_ij`** (series term at indices i, j) is a compound descriptive let-binding — not a single-letter set variable despite starting with `s`.
- **All hypothesis names** (`hA`, `hHermA`, `hHermPow`, `hcoord`, `h_taylor`, `h_deriv`, `hterm_nonneg`, `hterm_pos`, `h_perturb_posDef`, `h_continuous`, etc.) consistently follow the `h`-prefix convention.
- **No other violations** were found. The file is well-written with respect to the naming standards.

## GaussianRBF.lean

### Rules applied

1. **Types with mathematical content use uppercase letters** (style.md lines 22-24)
   - Inner product spaces / vector spaces: `E` (not `H`)

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `variable` declaration (line 21) | `H` | `E` | 1 | Type with `NormedAddCommGroup` and `InnerProductSpace ℝ` structure should use `E`, the standard letter for vector spaces |
| `innerProduct_is_pd_kernel` (line 30) | `H` | `E` | 1 | Consistent with section variable rename |
| `innerProduct_is_pd_kernel` let bindings (lines 39-40) | `H` | `E` | 1 | Type annotation for `v_a`, `v_b` follows section variable |
| `gaussian_rbf_pd_innerProduct_proof` (line 224) | `H` | `E` | 1 | Type annotation `fun h : H` updated to `fun h : E` |
| `gaussian_rbf_pd_innerProduct_proof` (lines 292-293) | `H` | `E` | 1 | Lambda type annotations for inner product and exp inner product PD kernel |

### Notes

- **`α`** in `IsPositiveDefiniteKernel`, `real_valued_PD_kernel_gives_PSD_matrix`, and `exp_is_pd_kernel` is compliant — generic type with no mathematical structure imposed in those signatures.
- **`K`** for a kernel function (`K : α → α → ℂ`) is compliant — uppercase for a named mathematical object (kernel) is standard notation.
- **`M`**, **`N`** for matrices (`Matrix (Fin m) (Fin m) ℝ`) are compliant — uppercase for types with mathematical content.
- **`m : ℕ`** is compliant — follows `m`, `n`, `k` convention for natural numbers.
- **`x`**, **`y`** for elements of a type are compliant — follows `x`, `y`, `z` convention.
- **`c`**, **`d`** for complex coefficient vectors are compliant — conventional mathematical notation for coefficients.
- **`a`**, **`b`** for real/imaginary parts of complex numbers are compliant — standard decomposition notation.
- **`v_a`**, **`v_b`** are compound descriptive let-bindings for weighted sums — not single-letter convention variables.
- **`i`**, **`j`** for sum indices are compliant — standard index variables.
- **`v`** for a real vector in `real_valued_PD_kernel_gives_PSD_matrix` is compliant — conventional for vectors.
- **`h`** in `fun h : E =>` (line 224) is compliant — element variable for the kernel argument (lowercase for elements of a type).
- **All hypothesis names** (`h_real`, `h_symm`, `hK`, `hM_psd`, `hExpM_psd`, `h_exp_eq`, `hN_psd`, `h_sum_eq`, `h_inner_pd`, `h_exp_inner_pd`, `expand_cc`, `re_prod`, `sum_re`, `split_sum`, `sum_a_eq`, `sum_b_eq`, `polar`, `factor`, `exp_real`, `star_exp`, `star_d`, `h_sum`, `h_sum'`) consistently follow the `h`-prefix convention or are descriptive compound names.
- **No other violations** were found.

## LaplaceIntegral.lean

### Rules applied

1. **Assumptions use `h`, `h₁`, ...** (style.md line 15) — local `have` bindings (proof terms / assumptions) should use the `h` prefix

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `complete_square` (line 456) | `expand` | `h_expand` | 1 | `have` binding (local proof of square expansion identity) must use `h` prefix |
| `laplace_integral_subst_sq` (line 486) | `key` | `h_key` | 1 | `have` binding (local proof that `(t^2)^(-1/2) = t⁻¹`) must use `h` prefix |

### Notes

- **`c`, `u`, `v`, `w`, `t`, `s`** (real-valued integration/substitution variables) are standard mathematical notation for the Laplace/Glasser integral context — compliant per lines 22-24.
- **`a`, `b`** (real parameters in the integral identity ∫ s^{-1/2} exp(-a/s - b·s) ds) are standard mathematical notation matching Gradshteyn & Ryzhik 3.471.9 — compliant per lines 22-24, not propositional variables.
- **`f`, `f'`, `g`** (local `let` bindings for functions in `weighted_glasser_integral_eq_gaussian` and `glasser_integral_substitution_identity`) are not assumptions, so the `h`-prefix rule does not apply.
- **All other `have` bindings** (`h_image`, `h_inj`, `h_deriv`, `h_cov`, `h_simp`, `h_meas`, `h_contOn`, `h_bound`, `h_gauss_int`, `h_ae_bound`, `h_base`, `h_int_image`, `h_anti`, `h_eq`, `h_neg`, `h_gaussian`, `h_abs`, `h1`–`h3`, `h_bdd`, `hu_pos`, `hu1`, `ht_pos`, `ht_ne`, `ht_nonneg`, `htsq_ne`, `h_pow_eq`, `h_rpow_nat`, `hcont`, `htop`, `hbot`, `hpc`, `hatTop_le`, `h_at_sqrt`, `h_sqrt_pos`, `h2pos`, etc.) consistently follow the `h`-prefix convention.
- **Index variables** (`i`, `j`) in sum binders are compliant — standard index variables.
- **Hypothesis parameters** (`hc`, `hu`, `ha`, `hb`, `ht`, `_hc`, `_ha`, `_hb`) all follow the `h`-prefix convention.
- **No other violations** were found. The file is well-written with respect to the naming standards.

## FourierTransforms.lean

### Rules applied

1. **Types with mathematical content use uppercase letters** (style.md lines 22-24)
   - Measure spaces: `X` (not lowercase `α`)
2. **Generic type variables use `α`, `β`, `γ`, ...** (style.md line 12) — `α` is reserved for generic types, not for real-valued parameters

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `variable` declaration (line 68) | `α` | `X` | 1 | Type with `MeasureSpace` structure should use uppercase; `X` is standard for measure spaces |
| `tripleReorder` (line 72) | `α` | `X` | 1 | Consistent with section variable rename |
| `measurePreserving_tripleReorder` (lines 76-89) | `α` | `X` | 1 | Consistent with section variable rename |
| `fubini_triple_reorder` (lines 98-132) | `α` | `X` | 1 | Consistent with section variable rename |
| `ik_add_ne_zero` (line 184) | `α : ℝ` | `a` | 2 | `α` is reserved for generic types; `a` is appropriate for a real-valued parameter |
| `ik_add_ne_zero` (line 184) | `hα` | `ha` | 2 | Hypothesis name follows renamed variable |
| `antideriv_exp_complex_linear` (line 200) | `α : ℝ` | `a` | 2 | `α` is reserved for generic types; `a` is appropriate for a real-valued parameter |
| `antideriv_exp_complex_linear` (line 200) | `hα` | `ha` | 2 | Hypothesis name follows renamed variable |
| Docstrings (lines 93, 183, 192-199) | `α` | `X` or `a` | 1, 2 | Updated to match renamed variables |

### Notes

- **`μ : ℝ`** (mass/decay rate parameter) is compliant — standard mathematical notation for physical parameters (style.md lines 22-24).
- **`k : ℝ`** (momentum/frequency variable) is compliant — conventional mathematical notation.
- **`x`, `y`** for elements of ℝ are compliant — follows `x`, `y`, `z` convention (style.md line 14).
- **`ξ : ℝ`** (Fourier dual variable) is compliant — standard mathematical notation in Fourier analysis.
- **`c : ℂ`** (complex coefficient, local `set` bindings) is compliant — conventional mathematical notation.
- **`F : X → X → X → ℂ`** is compliant — uppercase for a named function is standard mathematical notation.
- **`G : ℝ → ℂ`** (local `let` binding for integrand) is compliant — uppercase for named mathematical functions.
- **`a : ℝ`, `b : ℝ`** in `exp_pos_integrableOn_Iio` and `exp_pos_integrableOn_Iic` are compliant — real-valued parameters with no specific convention conflict.
- **`p`, `q`** used as pair/product-type bindings in `fun p =>`, `fun q =>` are compliant — idiomatic Lean/Mathlib usage for product elements.
- **`v : ℝ`** (integration variable in change-of-variables) is compliant.
- **`t : ℝ`** (derivative variable in `HasDerivAt`) is compliant.
- **`fL`, `fR`** (left/right function decompositions) are compound descriptive let-bindings — not single-letter convention variables.
- **Named argument syntax** `(α := X)` in calls to `MeasurableEquiv.prodAssoc` and `MeasurableEquiv.prodComm` refers to Mathlib's API parameter names, not our local variables.
- **All hypothesis names** (`hF`, `hμ`, `hc_re`, `hc_ne`, `hc_def`, `h_combine`, `h_split`, `h_Iic`, `h_Ioi`, `h_factor`, `h_rearrange`, `hinv`, `hRHS`, `hLHS`, `h_antideriv`, `h_tendsto`, `h_int`, `h_ftc`, `hdenom_ne`, `h_prod`, `h_cv`, `hG_eq`, `h_coeff`, `h_inner`, `h_char`, `h_eq`, `h_eq_real`, `h_int_real`, `h_lorentz`, `h_scale`, `hπ`, `hμ'`, `h2π`, `h2μ`, etc.) consistently follow the `h`-prefix convention.
- **No other violations** were found.

## BesselFunction.lean

### Rules applied

1. **`s`, `t`, ... for sets/lists** (style.md line 17-18) — `s` is reserved for sets/lists, not for real-valued lambda parameters
2. **`u`, `v`, `w`, ... for universes** (style.md line 11) — `v` is reserved for universes, not for real-valued lambda parameters
3. **`a`, `b`, `c`, ... for propositions** (style.md line 13) — `a`, `b` are reserved for propositions, not for real-valued elements
4. **`x`, `y`, `z`, ... for elements of a generic type** (style.md line 14) — the correct convention for real-valued lambda/intro variables

### Renames

| Location | Old name | New name | Rule | Reason |
|----------|----------|----------|------|--------|
| `besselK1_asymptotic`, `hF_deriv` (line 413) | `fun s =>` | `fun x =>` | 1, 4 | `s` is reserved for sets; real-valued `HasDerivAt` lambda parameter should use `x` |
| `besselK1_asymptotic`, `hF_deriv` (line 415) | `fun s =>` | `fun x =>` | 1, 4 | Same — `s` in composed `HasDerivAt` lambda |
| `besselK1_mul_self_le`, `hF_deriv` (line 609) | `fun s =>` | `fun x =>` | 1, 4 | `s` is reserved for sets; real-valued `HasDerivAt` lambda parameter should use `x` |
| `besselK1_mul_self_le`, `hF_deriv` (line 612) | `fun s =>` | `fun x =>` | 1, 4 | Same — `s` in composed `HasDerivAt` lambda |
| `bessel_symmetry_integral`, `h_strict_mono` (line 908) | `fun v =>` | `fun y =>` | 2, 4 | `v` is reserved for universes; real-valued lambda parameter should use `y` (`x` is used in the inner scope at line 911) |
| `bessel_symmetry_integral`, `hderiv` (lines 915-918) | `fun v =>` | `fun y =>` | 2, 4 | Consistent rename within the same `StrictMonoOn` function |
| `bessel_symmetry_integral`, `hderiv` (line 919) | `ext v` | `ext y` | 2, 4 | Consistent rename of extensionality variable |
| `bessel_symmetry_integral`, comment (line 922) | `fun v =>` | `fun y =>` | 2, 4 | Comment updated to match renamed variable |
| `bessel_symmetry_integral`, `hpow` (line 923) | `fun v : ℝ =>` | `fun y : ℝ =>` | 2, 4 | Consistent rename in `deriv_pow_field` lambda |
| `schwingerIntegral_eq_besselK1`, `hφ_mono` (line 1132) | `intro a b hab` | `intro x y hxy` | 3, 4 | `a`, `b` are reserved for propositions; elements of ℝ in `StrictMono` proof should use `x`, `y` |

### Notes

- **`z : ℝ`** (function argument in `besselK1`, `besselK1_pos`, etc.) is compliant — `x`, `y`, `z` convention for elements (style.md line 14).
- **`t : ℝ`** (integration variable) is compliant — standard mathematical notation for time/integration variables.
- **`u : ℝ`** (integration variable in `bessel_symmetry_integral`, `schwingerIntegral_eq_besselK1`) is compliant — standard mathematical notation for a substitution variable. While `u` is listed for universes (style.md line 11), it is used here as an element of ℝ with clear mathematical meaning; the universe convention applies to universe declarations, not to all uses of the letter.
- **`m : ℝ`** (mass parameter in `radial_besselK1_integrable`, `schwingerIntegral_eq_besselK1`) is compliant — standard mathematical notation for mass, taking precedence per lines 22-24.
- **`r : ℝ`** (radius parameter) is compliant — standard mathematical notation for radial distance.
- **`f`, `g`, `F`** (local `set`/`let` bindings for functions) are compliant — descriptive function names. `F` uppercase for antiderivative is standard mathematical convention.
- **`φ`** (substitution function) is compliant — standard mathematical notation.
- **`c`** (`let c := r / (2 * m)`) is compliant — conventional mathematical notation for a scaling constant.
- **`C`** (bound constants) is compliant — uppercase for mathematical constants is standard notation.
- **`z₀`** (point in `besselK1_continuousOn`) is compliant — subscripted variant of `z` for a fixed point.
- **`x`** in various `intro x hx`, `ext x` is compliant — elements of generic type.
- **`bound`** (local `set` binding for dominating function) is a compound descriptive name — not a single-letter convention variable.
- **All hypothesis names** (`hz`, `hm`, `hr`, `hf_def`, `hf_nonneg`, `hf_pos`, `hf_cont`, `hf_int`, `h_union`, `h_part1`, `h_part2`, `hbound_def`, `hbound'`, `hF_deriv`, `hF_cont`, `hF_tendsto`, `hg_int`, `hg_nonneg`, `h_bound`, `h_bound'`, `h_int_g`, `h_neg_F1`, `h_Ici_eq_Ioi`, `h_mono`, `hC_def`, `hC_pos`, `h_bound_int`, `hf_meas`, `h_nonneg`, `h_norm_bound`, `h_cosh_eq`, `h_cosh_lower`, `h_cosh_pos`, `h_exp_ge_usq`, `h_strict_mono`, `h_cosh_bound`, `h_transform`, `h_cov`, `h_eq`, `hφ_mono`, `hφ_surj`, `hφ_deriv`, etc.) consistently follow the `h`-prefix convention.
- **No other violations** were found.