/-
Concentricity/Corollaries.lean

The corollary layer, synchronized on 2026-09-02 to the zeta-specific
replacement surface recorded in the companion analysis repository
(Concentricity-Analysis, TASK-0004).

Formerly this file derived `cor:nontrivial` and `cor:rh` from the universal
theorem `ASection.concentricity`, which carried `sorryAx` through one admitted
pairwise read equality.  That universal proposition is false at the exact
`ASection` type (`SpecCandidate.current_ASection_concentricity_type_false`,
Concentricity/SpecCandidate.lean), so the unconditional corollaries were
withdrawn.  What is proved here, with axiom surface
`[propext, Classical.choice, Quot.sound]`:

* for `zetaSection`, a common centre for the complete enumerated
  upper-half-plane zero divisor is equivalent to the Riemann Hypothesis;
* pairwise equality of the certified transport reads of `zetaSection` is
  likewise equivalent to the Riemann Hypothesis;
* under the Riemann Hypothesis every such centre and read is `1/2`, and
  infinitely many zeros lie on the critical line.

These are geometric and categorical reformulations of RH.  They are not a
proof of RH, and nothing in this repository proves RH.

This file adds ZERO sorries and consumes no declaration carrying `sorryAx`.
-/
import Concentricity.ZetaSection
import Concentricity.ZetaDivisor
import Concentricity.RhEquiv
import Concentricity.Theorem
-- Kept so the root closure still builds the quarantined readout and
-- `ProjectiveTotal`; nothing below consumes it.
import Concentricity.ConcentricityReadout

noncomputable section

/-- **Zeta concentricity is RH** (master `thm:zeta-concentricity-rh`(a)):
centre equality for the complete enumerated upper-half-plane zeta divisor is
equivalent to Mathlib's `RiemannHypothesis`.  Completeness of the enumeration
is `zetaSphereZero_surjective`; both directions pass through the proved
`riemannHypothesis_iff_concentric` (`thm:rh-equiv`, RhEquiv.lean). -/
theorem zetaSection_concentric_iff_RH :
    ConcentricASection zetaSection ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨c, hc⟩
    apply riemannHypothesis_iff_concentric.mpr
    refine ⟨c, ?_⟩
    intro σ γ hγ hz
    obtain ⟨n, hn⟩ := zetaSphereZero_surjective ⟨hz, hγ⟩
    have hcentre := hc n
    change (zetaSphereZero n).re = c at hcentre
    rw [hn] at hcentre
    exact hcentre
  · intro hRH
    obtain ⟨c, hc⟩ := riemannHypothesis_iff_concentric.mp hRH
    refine ⟨c, fun n => ?_⟩
    change (zetaSphereZero n).re = c
    exact hc (zetaSphereZero_im_pos n) (zetaSphereZero_zero n)

/-- **The categorical read interface is RH-equivalent for zeta** (master
`thm:zeta-concentricity-rh`(b)): pairwise equality of the certified real
reads carried by the transport representatives of `zetaSection` is itself
equivalent to the Riemann Hypothesis.  It is therefore not a weaker bridge
that connectedness or the singleton component could supply. -/
theorem zetaSection_pairwiseTransportLevel_iff_RH :
    PairwiseTransportLevel zetaSection ↔ RiemannHypothesis := by
  calc
    PairwiseTransportLevel zetaSection ↔
        ConcentricASection zetaSection :=
      (concentricASection_iff_pairwiseTransportLevel zetaSection).symm
    _ ↔ RiemannHypothesis := zetaSection_concentric_iff_RH

/-- **Conditional centre** (master `thm:zeta-concentricity-rh`(c)): under
RH every enumerated zeta zero-sphere is centred at one half. -/
theorem zetaSection_sphereZero_re_eq_half_of_RH (hRH : RiemannHypothesis) :
    ∀ n : ℕ, (zetaSection.sphereZero n).re = (1 / 2 : ℝ) := by
  intro n
  change (zetaSphereZero n).re = (1 / 2 : ℝ)
  exact concentric_of_RH hRH (zetaSphereZero_im_pos n)
    (zetaSphereZero_zero n)

/-- The same conditional result at the certified categorical read. -/
theorem zetaSection_transportLevel_eq_half_of_RH
    (hRH : RiemannHypothesis) :
    ∀ n : ℕ, zetaSection.transportLevel n = (1 / 2 : ℝ) := by
  intro n
  rw [zetaSection.transportLevel_eq_sphereZero_re]
  exact zetaSection_sphereZero_re_eq_half_of_RH hRH n

/-- The critical-line infinitude clause, in the only form this repository
derives: under RH, the proved infinitude of nontrivial zeros
(`riemannZeta_nontrivialZeros_infinite`) lands on the line `Re s = 1/2`.
Hardy's unconditional theorem (master `thm:hardy`) is cited from the
literature and is not formalized here. -/
theorem zeta_criticalLine_zeros_infinite_of_RH (hRH : RiemannHypothesis) :
    {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2}.Infinite := by
  refine Set.Infinite.mono ?_ riemannZeta_nontrivialZeros_infinite
  intro s hs
  exact ⟨hs.1, hRH s hs.1 hs.2.1 hs.2.2⟩
