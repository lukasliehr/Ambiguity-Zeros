# Prescribed holes in the time frequency plane

This repository contains a Lean 4 formalization accompanying the paper *Prescribed holes in the time frequency plane and ptychographic phase retrieval* by Jaume de Dios Pont, Philippe Jaming, Lukas Liehr and Mitchell A. Taylor. The three main results of the paper are formalized in Lean.

## Formalized results

For $f \in L^2(\mathbb{R}^d)$ the ambiguity function of $f$ is defined by

```math
A(f)(x,\omega) = \int_{\mathbb{R}^d} f\left(t+\frac{x}{2}\right) \overline{f\left(t-\frac{x}{2}\right)} e^{-2\pi i \omega \cdot t} \, dt, \qquad (x,\omega) \in \mathbb{R}^d \times \mathbb{R}^d,
```

and $\mathcal{Z}(f)$ denotes the interior of the zero set of $A(f)$. A window $w \in L^2(\mathbb{R}^d)$ does phase retrieval if for all $f,g \in L^2(\mathbb{R}^d)$ the equality $|V_w f| = |V_w g|$ of the magnitudes of the short-time Fourier transforms implies that $g = e^{i\theta} f$ for some $\theta \in \mathbb{R}$.

**Theorem 1.1.** Let $w \in L^2(\mathbb{R}^d)$ be nonzero. If $\mathcal{Z}(w)$ is bounded, then $w$ does phase retrieval.

**Theorem 1.2.** Let $\Omega \subset \mathbb{R}^{2d}$ be bounded, nonempty and regular open, and let $a \in \mathbb{R}^{2d}$ be nonzero. There exists $b_0 > 0$ such that for every $0 < b < b_0$ one can find $f \in L^2(\mathbb{R}^d)$ with

```math
\mathcal{Z}(f) = (a + b\Omega) \cup (-(a + b\Omega)).
```

**Theorem 1.3.** There exist $0 < r < R < \infty$ such that no nonzero $f \in L^2(\mathbb{R})$ satisfies $O_{r,R} \subset \mathcal{Z}(f)$, where $O_{r,R}$ denotes the annulus of all $z \in \mathbb{R}^2$ with $r < |z| < R$.

The correspondence with the Lean declarations in the namespace `AmbiguityHoles` is:

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1 | `bounded_openZeros_phaseRetrieval` |
| Theorem 1.2 | `prescribed_openZeros` |
| Theorem 1.3 | `forbidden_annulus` |

## Lean entry points

- [Showcase.lean](Showcase.lean): a self-contained formulation of the three theorems, including the definitions of the ambiguity function, its open zero set, the short-time Fourier transform and phase retrieval. It imports only Mathlib and uses `sorry` in place of the proofs.
- [Showcase_WithProofs.lean](Showcase_WithProofs.lean): the same statements as in [Showcase.lean](Showcase.lean) with complete proofs, which are supplied by the internal library `LeanCode`. The three theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

The two showcase files declare the same theorem names and should not be imported together.

## Build

The project uses Lean `v4.29.0` and Mathlib `v4.29.0`, which are pinned in `lean-toolchain` and `lake-manifest.json`. From the repository root, run

```bash
lake exe cache get
lake build
```

The first command downloads the compiled Mathlib cache. The default targets are `LeanCode`, `Showcase` and `Showcase_WithProofs`. Building `Showcase` reports three uses of `sorry`, which are the intended placeholders.

The axioms of the three theorems and the agreement of the two showcase files can be checked with

```bash
lake build +LeanCode.Audit
python3 scripts/check_completion.py
```
