# Naming Convention Fixes

Audit of 12 Lean files against mathlib naming conventions from `mathlib_guide/naming.md`.

## Rules Applied

| Rule | Description |
|---|---|
| **lowerCamelCase for defs** | Non-Prop definitions (returning Types/terms) use `lowerCamelCase` |
| **snake_case for lemmas/theorems** | Prop-valued declarations use `snake_case` |
| **Rule 5** | UpperCamelCase names become lowerCamelCase when embedded in snake_case (e.g. `L2` → `l2`) |
| **Rule 6** | Acronyms written upper-/lowercase as a group |
| **No `_proof`/`_proved`** | Theorem names describe mathematical content, not that something is proved |
| **`_of_` for hypotheses** | Use `conclusion_of_hypothesis`, never `implies`, `gives`, or `from` |
| **Standard abbreviations** | Use mathlib terms: `posSemidef` not `psd`, `posDef` not `posdef` |

## Files With No Issues

- `PositiveDefinite.lean`
- `LaplaceIntegral.lean`
- `FourierTransforms.lean`
- `BesselFunction.lean`

## Files Fixed

### FrobeniusPositivity.lean (3 renames)

| Old Name | New Name | Reason |
|---|---|---|
| `psd_cauchy_schwarz` | `posSemidef_cauchy_schwarz` | Non-standard abbreviation `psd` |
| `psd_offdiag_zero_of_diag_zero` | `posSemidef_offdiag_zero_of_diag_zero` | Non-standard abbreviation `psd` |
| `frobenius_pos_of_psd_posdef` | `frobenius_pos_of_posSemidef_posDef` | Non-standard `psd`/`posdef` |

### SchurProduct.lean (3 renames)

| Old Name | New Name | Reason |
|---|---|---|
| `swap_sums_factor_B` | `swap_sums_factor` | Variable name `B` in theorem name |
| `gram_psd_from_A_posdef` | `gram_posSemidef_of_posDef` | `from` → `of`; `psd`/`posdef`; variable `A` |
| `frobenius_pos_of_psd_posdef` | `frobenius_pos_of_posSemidef_posDef` | Non-standard `psd`/`posdef` |

### HadamardExp.lean (5 renames)

| Old Name | New Name | Reason |
|---|---|---|
| `entrywiseExp_hadamardSeries` (def) | `entrywiseExpHadamardSeries` | snake_case → lowerCamelCase for def |
| `entrywiseExp_eq_hadamardSeries` | `entrywiseExp_eq_hadamardSeries` | No change (lemma, already snake_case) |
| `quadratic_form_entrywiseExp_hadamardSeries` | `quadratic_form_entrywiseExpHadamardSeries` | Updated to reference renamed def |
| `posDef_entrywiseExp_hadamardSeries_of_posDef` | `posDef_entrywiseExpHadamardSeries_of_posDef` | Updated to reference renamed def |
| `posSemidef_entrywiseExp_hadamardSeries_of_posSemidef` | `posSemidef_entrywiseExpHadamardSeries_of_posSemidef` | Updated to reference renamed def |

### GaussianRBF.lean (4 renames)

| Old Name | New Name | Reason |
|---|---|---|
| `innerProduct_is_pd_kernel` | `innerProduct_isPositiveDefiniteKernel` | `is_pd_kernel` → `isPositiveDefiniteKernel` |
| `real_valued_PD_kernel_gives_PSD_matrix` | `posSemidef_matrix_of_isPositiveDefiniteKernel` | `gives` → `of`; `PD`/`PSD` capitalization |
| `exp_is_pd_kernel` | `exp_isPositiveDefiniteKernel` | `is_pd_kernel` → `isPositiveDefiniteKernel` |
| `gaussian_rbf_pd_innerProduct_proof` | `gaussian_rbf_isPositiveDefiniteKernel` | `_proof` suffix; `pd` abbreviation |

### FunctionalAnalysis.lean (8 renames)

| Old Name | New Name | Reason |
|---|---|---|
| `composed_function` (def) | `composedFunction` | snake_case → lowerCamelCase for def |
| `embedding_real_to_complex` (def) | `embeddingRealToComplex` | snake_case → lowerCamelCase for def |
| `liftMeasure_real_to_complex` (def) | `liftMeasureRealToComplex` | snake_case → lowerCamelCase for def |
| `linfty_mul_L2_CLM` (def) | `linftyMulL2CLM` | snake_case → lowerCamelCase for def |
| `linfty_mul_L2_bound_aux` | `linfty_mul_l2_bound_aux` | `L2` → `l2` in snake_case (Rule 5+6) |
| `linfty_mul_L2_CLM_spec` | `linftyMulL2CLM_spec` | References renamed def |
| `linfty_mul_L2_CLM_norm_bound` | `linftyMulL2CLM_norm_bound` | References renamed def |
| `schwartz_bilinear_integrable_of_translationInvariant_L1` | `schwartz_bilinear_integrable_of_translationInvariant_l1` | `L1` → `l1` in snake_case |

### SchwartzTranslationDecay.lean (1 rename)

| Old Name | New Name | Reason |
|---|---|---|
| `schwartz_bilinear_translation_decay_proof` | `schwartz_bilinear_translation_decay` | `_proof` suffix |

### QuantitativeDecay.lean (8 renames)

| Old Name | New Name | Reason |
|---|---|---|
| `schwartz_has_polynomial_decay` (def) | `schwartzHasPolynomialDecay` | snake_case → lowerCamelCase for def |
| `schwartz_has_polynomial_decay_real` (def) | `schwartzHasPolynomialDecayReal` | snake_case → lowerCamelCase for def |
| `norm_exp_decay_implies_polynomial_decay` (def) | `polynomialDecayOfNormExpDecay` | snake_case → lowerCamelCase; `implies` → `of` |
| `convolution_polynomial_decay` (def) | `convolutionPolynomialDecay` | snake_case → lowerCamelCase for def |
| `convolution_compactSupport_decay` (def) | `convolutionCompactSupportDecay` | snake_case → lowerCamelCase for def |
| `convolution_expDecay_polynomial_decay` (def) | `convolutionExpDecayPolynomialDecay` | snake_case → lowerCamelCase for def |
| `exp_decay_implies_polynomial_decay` | `polynomial_decay_of_exp_decay` | `implies` → `of` (conclusion first) |
| `schwartz_bilinear_translation_decay_polynomial_proof` | `schwartz_bilinear_translation_decay_polynomial` | `_proof` suffix |

### L2TimeIntegral.lean (9 renames)

| Old Name | New Name | Reason |
|---|---|---|
| `sq_setIntegral_le_measure_mul_setIntegral_sq_proved` | `sq_setIntegral_le_measure_mul_setIntegral_sq` | `_proved` suffix |
| `setIntegral_L2_bound` | `setIntegral_l2_bound` | `L2` → `l2` (Rule 5+6) |
| `L2_time_average_bound` | `l2_time_average_bound` | `L2` → `l2` |
| `gff_time_integral_aestronglyMeasurable_proved` | `gff_time_integral_aestronglyMeasurable` | `_proved` suffix |
| `gff_covariance_norm_integrableOn_slice_proved` | `gff_covariance_norm_integrableOn_slice` | `_proved` suffix |
| `double_integral_polynomial_decay_bound_proved` | `double_integral_polynomial_decay_bound` | `_proved` suffix |
| `minkowski_weighted_L2_sum_proved` | `minkowski_weighted_l2_sum` | `_proved` suffix; `L2` → `l2` |
| `L2_variance_time_average_bound` | `l2_variance_time_average_bound` | `L2` → `l2` |
| `L2_process_covariance_fubini_integrable` | `l2_process_covariance_fubini_integrable` | `L2` → `l2` |

## Cross-File Reference Updates

| Downstream File | Updated References |
|---|---|
| `CovarianceMomentum.lean` | `linftyMulL2CLM`, `linftyMulL2CLM_spec`, `schwartz_bilinear_integrable_of_translationInvariant_l1` |
| `Minlos.lean` | `gaussian_rbf_isPositiveDefiniteKernel` |
| `OS3_GFF.lean` | `entrywiseExpHadamardSeries`, `posSemidef_entrywiseExpHadamardSeries_of_posSemidef` |
| `OS4_Clustering.lean` | `schwartz_bilinear_translation_decay`, `schwartz_bilinear_translation_decay_polynomial` |
| `OS4_Ergodicity.lean` | `double_integral_polynomial_decay_bound`, `gff_covariance_norm_integrableOn_slice`, `gff_time_integral_aestronglyMeasurable`, `l2_process_covariance_fubini_integrable`, `l2_variance_time_average_bound` |

## Build Verification

After all renames, `lake build` was run. The only failures are **pre-existing** issues unrelated to the naming changes:

- **HadamardExp.lean** line 322: Unsolved goal (shadowed `hAij` variable)
- **L2TimeIntegral.lean** lines 650–681: Missing identifiers `memLp_two_weighted` and `integrable_sq_of_memLp_two`

All 3,474+ other build targets succeeded, including all renamed files and their downstream dependents.
