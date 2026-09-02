/-
Concentricity/ASection.lean

`structure ASection` — the four-property package of master `def:A-section`,
in the stem encoding of Concentricity/StemRing.lean (R9: constructed, never
axiomatized; the compactified reading 𝕆* = S⁸ is the marked derivation node
of `rmk:compactify`).

Master `def:A-section` (verbatim): "An *A-section* is a section A of the ring
𝓡 of slice-preserving slice-regular functions on 𝕆* = S⁸ (Definition def:R)
— equivalently, a slice-preserving *semiregular* function on 𝕆* (the
meromorphic slice class; [SeriesExp §11]) — with the following four properties."
The four properties C1–C4 are quoted field-by-field below.

Statement-layer renderings (flagged for the author's skim, R6):
- Stem level: an A-section is carried by its intrinsic stem F : ℂ → ℂ
  (def:section-map: "one holomorphic stem with ℝ-valued components, the same
  for every I ∈ S⁶"); the residue-ℂ zero-spheres appear as the stem's
  conjugate zero pairs, enumerated by their upper-half-plane representatives.
- C3's slice-regular primary factors (prop:weierstrass; AdFslice Prop 3.1 +
  Thm 3.2, GV) are rendered at stem level by the classical elementary factors
  over conjugate pairs (`spherePrimary` below), with per-zero genus data.
- `∏'`/`Summable`/`∑'` are the bare (unconditional) forms, per the recon
  ruling on `SummationFilter`.

`sorry` marks UNFORMALIZED, never UNSOUND (R8).
-/
import Concentricity.StemRing
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Compactification.OnePoint.Basic

noncomputable section

open Complex

/-- The classical Weierstrass elementary factor
`E_p(w) = (1 - w) · exp(w + w²/2 + ⋯ + wᵖ/p)`. -/
def weierstrassE (p : ℕ) (w : ℂ) : ℂ :=
  (1 - w) * Complex.exp (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1))

/-- The stem-level primary factor of a residue-ℂ zero-sphere: the elementary
factors of the conjugate stem pair `{a, conj a}` (master C3's slice-regular
primary factor 𝓔(·; qₙ), prop:weierstrass; AdFslice Prop 3.1 + Thm 3.2, GV —
cited for faithfulness of the rendering, never as load). The product is
intrinsic in `z`. -/
def spherePrimary (p : ℕ) (a z : ℂ) : ℂ :=
  weierstrassE p (z / a) * weierstrassE p (z / starRingEnd ℂ a)

/-- Master `def:A-section`: the four-property package C1–C4, stem-encoded.
Each field's docstring quotes the master clause it transcribes. -/
structure ASection where
  /-- The intrinsic stem carrying the section (def:section-map): the
  underlying function of the A-section, slicewise `A(x + Iy) = F₁ + I·F₂`
  with `F = F₁ + iF₂` the stem. -/
  F : ℂ → ℂ
  /-- Slice preservation: the stem is intrinsic (def:slice-preserving). -/
  intrinsic : IsIntrinsic F
  /-- "equivalently, a slice-preserving *semiregular* function on 𝕆* (the
  meromorphic slice class; [SeriesExp §11])" — stem level: meromorphic on ℂ. -/
  meromorphic : MeromorphicOn F Set.univ
  /-- C1 data: the pole's location — "it … lies at a real point". -/
  pole : ℝ
  /-- C1: "A is meromorphically continued to 𝕆* with exactly one pole" —
  analytic away from the pole. -/
  c1_analyticAt : ∀ z : ℂ, z ≠ (pole : ℂ) → AnalyticAt ℂ F z
  /-- C1: "it is simple" — meromorphic order exactly −1 at the pole. (The
  clause "its value there is the point at infinity ∞ = N" is the compactified
  reading of the pole, `rmk:two-poles`.) -/
  c1_simple : meromorphicOrderAt F (pole : ℂ) = ((-1 : ℤ) : WithTop ℤ)
  /-- C2 data: the Euler index — "an *infinite* summable family {ℓ_p}". -/
  ι : Type
  /-- C2: the family is infinite. -/
  ι_infinite : Infinite ι
  /-- C2 data: the Euler family of stems. -/
  ℓ : ι → ℂ → ℂ
  /-- C2 data: the abscissa of the "slice right half-space Ω₀ ⊂ 𝕆*" —
  stem level: `{z | Ω₀ < re z}`. -/
  Ω₀ : ℝ
  /-- C2: the family members are slice-preserving (intrinsic stems). -/
  c2_intrinsic : ∀ p, IsIntrinsic (ℓ p)
  /-- C2: the family members are slice-regular on Ω₀. -/
  c2_analyticAt : ∀ p, ∀ z : ℂ, Ω₀ < z.re → AnalyticAt ℂ (ℓ p) z
  /-- C2: "each zero-free on Ω₀". -/
  c2_zero_free : ∀ p, ∀ z : ℂ, Ω₀ < z.re → ℓ p z ≠ 0
  /-- C2: "summable family" (bare `Summable` = unconditional, per the recon
  ruling). -/
  c2_summable : ∀ z : ℂ, Ω₀ < z.re → Summable fun p => ℓ p z
  /-- C2: "On a slice right half-space Ω₀ ⊂ 𝕆*, A = exp(∑_p ℓ_p)". -/
  c2_euler : ∀ z : ℂ, Ω₀ < z.re → F z = Complex.exp (∑' p, ℓ p z)
  /-- §4α (author-ruled transcription clarification, 2026-07-04): C2's
  "infinite Euler product" converges in the cited sources' sense — locally
  normally (Titchmarsh Ch. 1 register). The frozen pointwise `Summable` was
  an under-transcription of the master's meaning; the class does not change.
  Function-majorants on a ball; derivative majorants follow on the half-ball
  by Cauchy estimates. REGISTER NOTE (author's words, not re-encoded): the
  class is "even stronger — meromorphically continued through the infinity
  point and convergent"; that strength is already transcribed as C1 + the
  semiregular typing (def:R) and is deliberately not duplicated here. -/
  c2_locMajorant : ∀ z : ℂ, Ω₀ < z.re → ∃ r > 0, ∃ u : ι → ℝ, Summable u ∧
    ∀ p, ∀ w ∈ Metric.ball z r, ‖ℓ p w‖ ≤ u p
  /-- C3 data: "q is the octonionic coordinate, m ≥ 0" — the order of the
  zero at the origin. -/
  m : ℕ
  /-- C3 data: "R is the slice-regular Weierstrass product over the
  residue-ℝ (real) zeros of A, vanishing only on ℝ". -/
  Rfac : ℂ → ℂ
  /-- C3 data: "g is slice-preserving entire". -/
  gfac : ℂ → ℂ
  /-- C3 data: the genus of each primary factor (part of "the slice-regular
  Weierstrass primary factor of qₙ", prop:weierstrass / GV). -/
  genus : ℕ → ℕ
  /-- C3 data: "{qₙ} enumerates the residue-ℂ zero-spheres of A" — stem
  level: the upper-half-plane representatives of the conjugate zero pairs. -/
  sphereZero : ℕ → ℂ
  /-- C3: R is slice-preserving. -/
  c3_R_intrinsic : IsIntrinsic Rfac
  /-- C3: R is entire (stem level). -/
  c3_R_entire : Differentiable ℂ Rfac
  /-- C3: R vanishes only at the **nonzero** residue-ℝ zeros (the C3 one-word
  repair, author-ruled 2026-07-04: "R is the slice-regular Weierstrass product
  over the nonzero residue-ℝ zeros" — `q^m` alone carries the origin). Zeros of
  R are real and nonzero. Load-bearing for PLAN §6's gauge caveat: a slid
  origin is a nonzero real zero, absorbable into R. -/
  c3_R_zeros_real : ∀ z : ℂ, Rfac z = 0 → z.im = 0 ∧ z ≠ 0
  /-- C3: g is slice-preserving. -/
  c3_g_intrinsic : IsIntrinsic gfac
  /-- C3: "g is slice-preserving entire". -/
  c3_g_entire : Differentiable ℂ gfac
  /-- C3: the zero-spheres are residue-ℂ — non-real; upper-half-plane
  representatives. -/
  c3_sphere_nonreal : ∀ n, 0 < (sphereZero n).im
  /-- C3: the infinite product converges (bare `Multipliable` =
  unconditional, per the recon ruling). -/
  c3_multipliable : ∀ z : ℂ, Multipliable fun n => spherePrimary (genus n) (sphereZero n) z
  /-- §4α (author-ruled transcription clarification, 2026-07-04): C3's
  "Weierstrass factorization" converges in the cited sources' sense —
  locally normally (AdF/prop:weierstrass register). Same clarification as
  `c2_locMajorant`; the class does not change. -/
  c3_locMajorant : ∀ z : ℂ, z ≠ (pole : ℂ) → ∃ r > 0, ∃ u : ℕ → ℝ, Summable u ∧
    ∀ n, ∀ w ∈ Metric.ball z r,
      ‖spherePrimary (genus n) (sphereZero n) w - 1‖ ≤ u n
  /-- The L4 lower edge (C-1 fork ruling (β), author, 2026-07-04):
  CLARIFICATION-PENDING-DERIVATION — the divisor's real parts are bounded
  below. With the quadratic point-density of `c3_locMajorant` this implies
  Sekatskii's condition (ii), closing C-1 by the worked paired expansion.
  R9 price of deletion (author's wording, verbatim): "deleted the day (γ)
  derives it from the semiregular-on-𝕆* typing; if underivable, this is a
  flagged class hypothesis and the master gains the clause." The (γ)
  derivation question — GPS Def. 11.1 (poles are isolated: N's typing when
  zeros accumulate to it), master def:R + rmk:compactify, SCAN §7(iv) — is
  Lane B's opening task; master wording waits for γ's verdict either way.
  ζ instantiates with its classical strip (member-private, legitimate). -/
  c3_lowerEdge : ∃ βlo : ℝ, ∀ k : ℕ, βlo ≤ (sphereZero k).re
  /-- **C3 THROUGH N** (§4α transcription, third instance of the pattern after
  `c2_locMajorant`/`c3_locMajorant`; author-ruled register, 2026-07-06). The
  master's C3 asserts the through-the-pole product "converging locally normally
  on 𝕆* ∖ {p₀}" (`def:A-section` C3; `prop:weierstrass` — "convergence of the
  infinite products is part of the cited statement") — a domain that INCLUDES N,
  where the divisor accumulates (SCAN §7(iv): C4 + compactness of S⁸ + C1's
  cone). Read at N in the chart `def:R`'s slice-sphere typing provides
  (f(Ω_v) ⊆ ℂ_v*; `rmk:compactify` — the section functor is the natural round
  trip from the domain 𝕆* through the continuum of slice Riemann spheres back
  into 𝕆*), the clause's divisor-side content is the summability of the
  zero-spheres' squared chart-norms at N — stated totally as the quadratic
  point-density at 0. REGISTER (author): this clause is NOT level-blind — it
  directly ATTACHES all the levels; that is what makes an A-section special
  where the general ring over the base 𝓑 is not. Every mirror circle closes
  through the one N (the kernel's unit circle is the great circle; the kernel
  of the unit imaginary octonions is degenerate exp — band and circle
  inseparable), so this single clause serves every anchor pair: it is the D0
  rung of the ladder that closes Island P. NOT a new hypothesis: the reading
  of a printed clause of `def:A-section` at one point of its stated domain.
  ζ discharges it by `zetaSphereZero_density` (Jensen + dyadic shells,
  ZetaDensityCore.lean). -/
  c3_atN : Summable fun n => 1 / (1 + ‖sphereZero n‖ ^ 2)
  /-- C3: "On 𝕆* ∖ {pole}, A = qᵐ · R · e^g · ∏ₙ 𝓔(·; qₙ)" — over the **full
  divisor**, which includes the pole with multiplicity −1 (PLAN §8, author-ruled
  transcription repair 2026-07-04: classically Hadamard factors (s−1)ζ(s); the
  frozen entire-shaped form collided with `c1_simple` under the convergence
  upgrade and made `cor:zeta-section` unbuildable — the pole factor is what lets
  the one meromorphic object carry both infinite families against the single
  pole). -/
  c3_factorization : ∀ z : ℂ, z ≠ (pole : ℂ) →
    (z - (pole : ℂ)) * F z = z ^ m * Rfac z * Complex.exp (gfac z) *
      ∏' n, spherePrimary (genus n) (sphereZero n) z
  /-- C4: "Infinitely many residue-ℂ zeros. The index set {qₙ} is
  infinite." -/
  c4_infinite : (Set.range sphereZero).Infinite
  /-- The compactified value at ∞ = N — data of the section as a map on
  𝕆* = S⁸ that the stem alone does not determine (the marked compactification
  node, `rmk:compactify`). It is assigned data: no continuity or meromorphy at
  the domain point N is required by this structure, and none holds for
  `zetaSection` (master `def:A-section` C1 and `def:zeta-Cstar`, corrected
  2026-09-02; the earlier docstring's "continuation through infinity" was
  withdrawn with them). -/
  valueAtInfinity : OnePoint ℂ
  /-- `def:section-map`(ii): "A(N) ∈ ⋂_I ℂ_I* = ℝ ∪ {N} by (i)" — at stem
  level: the value at ∞, when finite, is real. (Derived in the master from
  slice preservation of values; carried here as a field of the compactified
  data, per `rmk:compactify`.) -/
  valueAtInfinity_real : ∀ z : ℂ, valueAtInfinity = (z : OnePoint ℂ) → z.im = 0

namespace ASection

/-- C2's closing clause, DERIVED (R10): "in particular A is zero-free on
Ω₀" — the exponential never vanishes. -/
theorem zero_free_on_halfSpace (A : ASection) {z : ℂ} (hz : A.Ω₀ < z.re) :
    A.F z ≠ 0 := by
  rw [A.c2_euler z hz]
  exact Complex.exp_ne_zero _

/-- The stem of an A-section is real on the real axis (def:section-map:
"A(ℝ) ⊆ ℝ"). DERIVED (R10), inherited from intrinsicality. -/
theorem real_on_real (A : ASection) (x : ℝ) : (A.F x).im = 0 :=
  StemRing.real_on_real A.intrinsic x

end ASection
