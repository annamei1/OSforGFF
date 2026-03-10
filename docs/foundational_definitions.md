# Foundational Definitions and Axioms

This document catalogs all core definitions, structures, and axioms in the OSforGFF project
for human review. Helper lemmas and theorems are omitted; only the objects on which the
construction is built are listed.

---

## Axioms (3 total)

These are the only `axiom` declarations in the project. Everything else is proved.

| Axiom | File | Description |
|-------|------|-------------|
| `schwartz_nuclear` | [Measure/NuclearSpace.lean:145](../OSforGFF/Measure/NuclearSpace.lean#L145) | Schwartz space S(E, F) is nuclear for any finite-dimensional E. Well-known (Gel'fand–Vilenkin, Trèves), not yet in Mathlib. |
| `minlos_theorem` | [Measure/Minlos.lean:73](../OSforGFF/Measure/Minlos.lean#L73) | A continuous positive-definite normalized functional on a nuclear space is the characteristic functional of a unique probability measure on the topological dual. (Minlos 1959) |
| `differentiable_analyticAt_finDim` | [OS/OS0_Analyticity.lean:86](../OSforGFF/OS/OS0_Analyticity.lean#L86) | A ℂ-differentiable function on a finite-dimensional complex vector space is analytic (Goursat/Hartogs in n dimensions). |

---

## Spacetime and Test Functions

### Core types (`Spacetime/Basic.lean`)

| Line | Name | Definition |
|------|------|------------|
| 56 | `STDimension` | `abbrev STDimension := 4` — spacetime dimension |
| 57 | `SpaceTime` | `EuclideanSpace ℝ (Fin STDimension)` — Euclidean ℝ⁴ |
| 78 | `TestFunction` | `SchwartzMap SpaceTime ℝ` — real Schwartz functions S(ℝ⁴, ℝ) |
| 80 | `TestFunctionℂ` | `SchwartzMap SpaceTime ℂ` — complex Schwartz functions S(ℝ⁴, ℂ) |
| 111 | `FieldConfiguration` | `WeakDual ℝ (SchwartzMap SpaceTime ℝ)` — tempered distributions S'(ℝ⁴) |
| 268 | `SpatialCoords` | `EuclideanSpace ℝ (Fin (STDimension - 1))` — spatial ℝ³ |
| 271 | `SpatialL2` | `Lp ℝ 2 (volume : Measure SpatialCoords)` — L²(ℝ³) |

### Pairings and generating functionals (`Spacetime/Basic.lean`)

| Line | Name | Definition |
|------|------|------------|
| 122 | `distributionPairing` | `⟨ω, f⟩ : ℝ` — evaluation of distribution ω on test function f |
| 163 | `GJGeneratingFunctional` | `Z[J] = ∫ exp(i⟨ω,J⟩) dμ(ω)` — Glimm–Jaffe generating functional |
| 249 | `distributionPairingℂ_real` | `⟨ω, f⟩ₗ = ⟨ω, fᵣₑ⟩ + i⟨ω, fᵢₘ⟩` — complex pairing |
| 256 | `GJGeneratingFunctionalℂ` | Complex generating functional for complex test functions |
| 261 | `GJMean` | `𝔼_μ[⟨ω, φ⟩]` — mean field |
| 279 | `E` | `E(m, k) = √(‖k‖² + m²)` — relativistic dispersion relation |

### Complex test functions (`Spacetime/ComplexTestFunction.lean`)

| Line | Name | Definition |
|------|------|------------|
| 218 | `toComplex` | Embedding ℝ-Schwartz → ℂ-Schwartz |
| 308 | `conjSchwartz` | Pointwise complex conjugation on Schwartz functions |

### Spacetime decomposition (`Spacetime/Decomposition.lean`)

| Line | Name | Definition |
|------|------|------------|
| 49 | `spacetimeDecomp` | Measurable equivalence SpaceTime ≃ᵐ ℝ × SpatialCoords |

---

## Discrete Symmetries (`Spacetime/DiscreteSymmetry.lean`)

| Line | Name | Definition |
|------|------|------------|
| 58 | `QFT.timeReflection` | Θ: (t, x̄) ↦ (−t, x̄) on spacetime |
| 72 | `QFT.timeReflectionIsometry` | Θ as element of O(4) |
| 125 | `QFT.timeReflectionLE` | Θ as linear isometry equivalence (self-inverse) |
| 176 | `QFT.compTimeReflection` | Pullback f ↦ f∘Θ on complex test functions (CLM) |
| 185 | `QFT.compTimeReflectionReal` | Pullback f ↦ f∘Θ on real test functions (CLM) |

---

## Euclidean Group (`Spacetime/Euclidean.lean`)

| Line | Name | Definition |
|------|------|------------|
| 51 | `QFT.O4` | Orthogonal group O(4) = linear isometries of ℝ⁴ |
| 56 | `QFT.E` | `structure` — Euclidean motion (R ∈ O(4), t ∈ ℝ⁴), i.e. E(4) = ℝ⁴ ⋊ O(4) |
| 62 | `QFT.act` | Group action x ↦ R·x + t |
| 350 | `QFT.euclidean_action` | Pullback (g·f)(x) = f(g⁻¹·x) on complex test functions |
| 385 | `QFT.euclidean_action_CLM` | Euclidean action as a continuous linear map |

---

## Time Translation (`Spacetime/TimeTranslation.lean`)

| Line | Name | Definition |
|------|------|------------|
| 70 | `timeShift` | (t, x̄) ↦ (t+s, x̄) on spacetime |
| 199 | `timeTranslationSchwartzCLM` | T_s as CLM on real Schwartz functions |
| 874 | `timeTranslationDistribution` | T_s on distributions by duality: ⟨T_s ω, f⟩ = ⟨ω, T_{−s} f⟩ |

---

## Positive-Time Test Functions and OS Star (`Spacetime/PositiveTimeTestFunction.lean`)

| Line | Name | Definition |
|------|------|------------|
| 42 | `HasPositiveTime` | Predicate: x₀ > 0 |
| 52 | `PositiveTimeTestFunctions.submodule` | Submodule of f ∈ S(ℝ⁴) with tsupport ⊆ {x₀ > 0} |
| 67 | `PositiveTimeTestFunction` | Type alias for positive-time test functions |
| 83 | `PositiveTimeTestFunctionsℂ.submodule` | ℂ-submodule of f ∈ S(ℝ⁴, ℂ) with tsupport ⊆ {x₀ > 0} |
| 98 | `PositiveTimeTestFunctionℂ` | Type alias for complex positive-time test functions |
| 130 | `starTestFunction` | OS star: (star f)(x) = conj(f(Θ x)) — time reflection + conjugation |

---

## Free Covariance

### Momentum space (`Covariance/Momentum.lean`)

| Line | Name | Definition |
|------|------|------------|
| 122 | `freePropagatorMomentum` | P(k) = 1/(‖k‖² + m²) — free propagator (physics convention) |
| 134 | `freePropagatorMomentum_mathlib` | 1/((2π)²‖k‖² + m²) — Mathlib Fourier convention |
| 162 | `freeCovariance_regulated` | UV-regulated covariance: Fourier integral of P(k)·e^{−α‖k‖²} |
| 195 | `schwingerIntegrand` | exp(−t(‖k‖² + m²)) — Schwinger proper-time integrand |
| 230 | `heatKernelPositionSpace` | (4πt)^{−d/2} exp(−r²/(4t)) — position-space heat kernel |
| 406 | `covarianceSchwingerRep` | ∫₀^∞ e^{−tm²} H(t,r) dt — Schwinger representation |
| 456 | `freeCovarianceBessel` | (m/4π²r)·K₁(mr) — Bessel form of free covariance |
| 462 | `freeCovariance` | **Principal alias** for the two-point function C(x,y) |
| 2159 | `momentumWeightSqrt` | 1/√(‖k‖² + m²) — square-root propagator |
| 2281 | `momentumWeightSqrt_mul_CLM` | Multiplication by √P as bounded operator on L² |

### Position space (`Covariance/Position.lean`)

| Line | Name | Definition |
|------|------|------------|
| 59 | `heatKernelMomentum` | Spatial heat kernel: exp(−t·E(k))/E(k) |
| 580 | `freeCovarianceℂ_regulated` | Regulated complex bilinear form with UV cutoff |
| 597 | `freeCovarianceℂ` | ∫∫ f̄(x) C(x,y) g(y) dx dy — complex covariance bilinear form |

### Real form and embedding (`Covariance/RealForm.lean`)

| Line | Name | Definition |
|------|------|------------|
| 47 | `freeCovarianceFormR` | ∫∫ f(x) C(x,y) g(y) dx dy — real covariance bilinear form |
| 89 | `sqrtPropagatorMap` | T: f ↦ FT(f)·(‖k‖²+m²)^{−1/2} — embedding into L² |
| 270 | `embeddingMap` | ℝ-linear embedding T: TestFunction → L² |
| 297 | `embeddingMapCLM` | Continuous linear version of the embedding |

### Parseval / Fourier (`Covariance/Parseval.lean`)

| Line | Name | Definition |
|------|------|------------|
| 138 | `physicsFourierTransform` | f̂(k) = ∫ f(x) e^{−i⟨k,x⟩} dx |

---

## Schwinger Functions (`Schwinger/`)

### n-point functions (`Schwinger/Defs.lean`)

| Line | Name | Definition |
|------|------|------------|
| 57 | `SchwingerFunction` | S_n(f₁,…,fₙ) = ∫ ∏ᵢ ⟨ω, fᵢ⟩ dμ(ω) — n-point correlation |
| 62 | `SchwingerFunction₁` | 1-point function (mean field) |
| 67 | `SchwingerFunction₂` | 2-point function (covariance) |
| 109 | `CovarianceBilinear` | Property: S₂ is ℂ-bilinear |
| 258 | `IsGaussianMeasure` | Z[J] = exp(−½ Cov(J,J)) for all J |

### Pointwise 2-point function (`Schwinger/TwoPoint.lean`)

| Line | Name | Definition |
|------|------|------------|
| 67 | `SmearedTwoPointFunction` | Bump-regularized 2-point function |
| 102 | `SchwingerTwoPointFunction` | Pointwise 2-point function as limit of smeared correlations |

---

## Measure Construction (`Measure/`)

### Nuclear space (`Measure/NuclearSpace.lean`)

| Line | Name | Definition |
|------|------|------------|
| 45 | `IsNuclearMap` | A CLM is nuclear (trace-class): T = ∑ₙ φₙ(·)·yₙ with ∑‖φₙ‖·‖yₙ‖ < ∞ |
| 126 | `NuclearSpace` | `class` — topology generated by Hilbertian seminorms with Hilbert–Schmidt inclusions |

### Minlos theorem (`Measure/Minlos.lean`)

| Line | Name | Definition |
|------|------|------------|
| 100 | `gaussian_characteristic_functional` | Φ(f) = exp(−½⟨f, Cf⟩) |

### Covariance form structure (`Measure/MinlosAnalytic.lean`)

| Line | Name | Definition |
|------|------|------------|
| 52 | `CovarianceForm` | `structure` — symmetric positive-semidefinite bilinear form Q with positive-definite Gaussian CF |

### GFF construction (`Measure/Construct.lean`)

| Line | Name | Definition |
|------|------|------------|
| 85 | `isCenteredGJ` | 𝔼[⟨ω, f⟩] = 0 for all f |
| 90 | `isGaussianGJ` | Z[J] = exp(−½ S₂(J,J)) |
| 129 | `gaussianFreeField_free` | **The GFF measure** μ_GFF(m) on S'(ℝ⁴), constructed via Minlos |
| 322 | `freeCovarianceForm` | The free covariance packaged as a `CovarianceForm` |

---

## OS Axiom Definitions (`OS/Axioms.lean`)

| Line | Name | Definition |
|------|------|------------|
| 73 | `OS0_Analyticity` | Z[∑ zᵢJᵢ] is analytic on ℂⁿ |
| 83 | `OS1_Regularity` | ‖Z[f]‖ ≤ exp(c·‖f‖_Lp) |
| 91 | `OS2_EuclideanInvariance` | Z[f] = Z[g·f] for all g ∈ E(4) |
| 109 | `OS3_ReflectionPositivity` | Re(∑ c̄ᵢcⱼ Z_ℂ[fᵢ − star fⱼ]) ≥ 0 for complex positive-time fᵢ, star f = conj∘f∘Θ |
| 123 | `OS4_Clustering` | Z[f + τ_a g] → Z[f]·Z[g] as ‖a‖ → ∞ |
| 136 | `OS4_Ergodicity` | (1/T)∫₀ᵀ A(T_s ω) ds →_{L²} 𝔼[A] |
| 173 | `SatisfiesAllOS` | `structure` — bundles OS0–OS4 |

### Master theorem (`OS/Axioms.lean`)

```
theorem gaussianFreeField_satisfies_all_OS_axioms (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF m)
```

---

## General Mathematics (`General/`)

| File | Line | Name | Definition |
|------|------|------|------------|
| BesselFunction.lean | 47 | `besselK1` | Modified Bessel function K₁(z) |
| PositiveDefinite.lean | 36 | `IsPositiveDefinite` | ∑ c̄ᵢcⱼ φ(xᵢ−xⱼ) ≥ 0 |
| GaussianRBF.lean | 35 | `IsPositiveDefiniteKernel` | ∑ c̄ᵢcⱼ K(xᵢ,xⱼ) ≥ 0 |
| FunctionalAnalysis.lean | 245 | `schwartzToL2` | Continuous embedding S(ℝᵈ) ↪ L²(ℝᵈ) |
| FunctionalAnalysis.lean | 804 | `SchwartzMap.translate` | f.translate(a)(x) = f(x−a) |
