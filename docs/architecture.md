# Architecture

How the 47 files fit together. For proof details see the paper (§4).

## Dependency layers

```
General ──→ Spacetime ──→ Covariance ──→ Schwinger ──→ Measure ──→ OS
  (12)        (9)           (4)           (3)           (6)       (12)
```

Imports flow left to right with one cross-cutting edge:

- `Measure/IsGaussian` imports `OS/OS0_Analyticity` to use the proved
  analyticity for the identity-theorem argument S₂ = C.

This is not circular: OS0 depends on `Measure/Construct` (the measure must
exist before we can prove analyticity), and `IsGaussian` feeds back into
the later OS proofs (OS1–OS4 need S₂ = C).

## Three assumed axioms

| Axiom | Why needed | Difficulty to prove |
|-------|-----------|-------------------|
| `schwartz_nuclear` | Minlos requires a nuclear source space | Hard — needs the full Hilbert–Schmidt embedding theory for Schwartz seminorms |
| `minlos_theorem` | Existence + uniqueness of the GFF measure | Hard — Gel'fand–Vilenkin proof uses projective limits of finite-dim Gaussians |
| `differentiable_analyticAt_finDim` | Hartogs' theorem for OS0 | Medium — needs Cauchy integral formula in several variables; partially in Mathlib |

Everything else is proved. The `#print axioms` output for the master theorem
shows exactly these three plus the standard Lean/Mathlib axioms (propext, Quot.sound, Classical.choice).

## OS3: the longest proof chain

OS3 (reflection positivity) is the most technically involved axiom, spanning
4 files and ~7100 lines. The logical chain:

1. **MixedRepInfra** (~3800 lines): Schwinger parametrization makes all
   integrals absolutely convergent (the naive momentum-space approach fails
   because 1/√(k²+m²) is not L¹ in 3D). Proves ~36 Fubini exchange and
   integrability lemmas.

2. **MixedRep** (~1900 lines): Chains the exchanges to reach the mixed
   representation ⟨Θf, Cf⟩ = ∫ (1/ω)|F_ω(k̄)|² dk̄, going through
   heat kernel → Fourier → Gaussian k₀ integral → Laplace transform.

3. **CovarianceRP** (~460 lines): Defines the star operation
   `(star f)(x) = conj(f(Θx))` on complex test functions and proves
   `Re⟨star f, Cf⟩ ≥ 0` for positive-time f.  The factorization
   |−x₀−y₀| = x₀+y₀ for positive-time support makes the integrand a
   perfect square.  Bridges to real test functions via
   `star (toComplex f) = compTimeReflection (toComplex f)`.

4. **ReflectionPositivity** (~1020 lines): Two independent proofs.

   **Real version** (lines 52–530): Schur–Hadamard lift for real coefficients:
   R_ij = ⟨Θfᵢ, Cfⱼ⟩ is PSD → exp(R) is PSD (Hadamard series) →
   ∑ cᵢcⱼ Z[fᵢ−Θfⱼ] ≥ 0.

   **Complex version** (lines 532–1023): Full Osterwalder–Schrader formulation
   with complex test functions and complex coefficients.  The matrix entry
   factorizes as Z_ℂ[fᵢ − star fⱼ] = Aᵢ · conj(Aⱼ) · exp(Rᵢⱼ) where
   Rᵢⱼ = C(fᵢ, star fⱼ) is Hermitian PSD.  Key ingredients:
   - `star` antilinearity: star(∑ c̄ⱼfⱼ) = ∑ cⱼ star(fⱼ)
   - Hermiticity: R_{ji} = conj(R_{ij}) via C(star f, star g) = conj(C(f,g))
   - Complex Schur product theorem (Kronecker ⊗ diagonal submatrix)
   - Complex entrywise exponential PSD via Hadamard power series limit

## OS4: two-stage argument

1. **Clustering** (OS4_Clustering): Gaussian factorization reduces the
   clustering bound to estimating S₂(f, T_{−s}g), which decays as
   (1+|s|)^{−α} by Schwartz convolution decay with the exponential kernel
   e^{−m|x|}.

2. **Ergodicity** (OS4_Ergodicity): Polynomial clustering with α = 6 feeds
   into an L² time-average bound: ‖(1/t)∫₀ᵗ A(T_s φ) ds − 𝔼[A]‖² ≤ C/t → 0.

## Key design choices

- **Schwartz over D**: We use S(ℝ⁴) rather than D(ℝ⁴) because Mathlib has
  SchwartzSpace but not test function spaces with compact support. Since
  D ⊂ S and S' ⊂ D', our axioms imply the Glimm–Jaffe versions.

- **Schwinger parametrization for OS3**: The direct momentum-space Fubini
  fails (conditional convergence). The Schwinger representation
  C = ∫₀^∞ e^{−sm²} H_s ds introduces the heat kernel as a regularizer,
  making all integrals absolutely convergent.

- **Gaussian regulator for Parseval**: A factor e^{−α|k|²} is introduced
  in the Parseval identity and removed as α → 0⁺, avoiding convergence
  issues with the bare propagator 1/(|k|²+m²) in L¹.

- **Bessel K₁ for position-space covariance**: Rather than Fourier-transforming
  the propagator directly (conditionally convergent), we define C(x,y) via
  the closed-form (m/4π²r)K₁(mr) and prove it equals the Schwinger integral.
