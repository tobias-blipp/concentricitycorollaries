import Concentricity.Theorem
import Concentricity.ASectionCResidueDiagram
import Concentricity.ASectionTotalActionState
import Concentricity.Corollaries
import Concentricity.SpecCandidate

noncomputable section

open CategoryTheory

/- TARGET-FIRST GATE, synchronized 2026-09-02.  The former outer declaration
`ASection.concentricity` was withdrawn (its universal statement is false at
this `ASection` type).  The headline surface is now the zeta-specific
equivalence and the countermodel; nothing below counts until these compile. -/
example : ConcentricASection zetaSection ↔ RiemannHypothesis :=
  zetaSection_concentric_iff_RH
example : ¬ ∀ A : ASection, ∃ c : ℝ, ∀ n : ℕ, (A.sphereZero n).re = c :=
  SpecCandidate.current_ASection_concentricity_type_false

/- The read-set suppliers, at their real names. -/
#check @ASection.transportLevel
#check @ASection.AsectionCResidueDiagram
#check @ASection.AsectionCResidueInclusion
#check @ASection.IsCResidueState
#check @ASection.IsNorthCResidueState
#check @ASection.residueTotal
#check @ASection.sphereZero_mem_CResidueZeroLocus
#check @pi0Functor
#check @pi0GrothendieckEquiv
#check @CategoryTheory.ConnectedComponents
#check @CategoryTheory.isPreconnected_zigzag

/- THE ι_A-ONWARD LEDGER (kernel receipts, raw).  Every line below must
print exactly [propext, Classical.choice, Quot.sound]; since 2026-09-02 the
repository contains no `sorry`. -/
#print axioms ASection.IsNorthCResidueState
#print axioms ASection.IsCResidueState
#print axioms ASection.AsectionCResidueTransport
#print axioms ASection.AsectionCResidueDiagram
#print axioms ASection.AsectionCResidueInclusion
#print axioms ASection.residueActionState
#print axioms ASection.residueActionState_positioned
#print axioms ASection.residueTotal
#print axioms ASection.residueTotal_value_back
#print axioms ASection.sphereZero_mem_CResidueZeroLocus
#print axioms ASection.CResidueZeroLocus_infinite
#print axioms pi0Functor
#print axioms pi0GrothendieckEquiv
#print axioms pi0_grothendieck
#print axioms ASection.transportLevel
#print axioms ASection.sweepTransitive_on_residueSystem
#print axioms ASection.residueTotal_isConnected
#print axioms ASection.residueTotal_pi0_singleton
#print axioms ASection.residueTotal_pi0_colimit_singleton
#print axioms concentricASection_iff_pairwiseTransportLevel

/- THE ZETA-SPECIFIC REPLACEMENT SURFACE (Corollaries.lean). -/
#print axioms zetaSection_concentric_iff_RH
#print axioms zetaSection_pairwiseTransportLevel_iff_RH
#print axioms zetaSection_sphereZero_re_eq_half_of_RH
#print axioms zetaSection_transportLevel_eq_half_of_RH
#print axioms zeta_criticalLine_zeros_infinite_of_RH

/- THE COUNTERMODEL (SpecCandidate.lean). -/
#print axioms SpecCandidate.candidateSection
#print axioms SpecCandidate.candidateSection_not_concentric
#print axioms SpecCandidate.current_ASection_concentricity_type_false
#print axioms SpecCandidate.candidateSection_not_pairwiseTransportLevel
