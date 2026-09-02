/-
Concentricity/Theorem.lean

The π₀ lemma (master `lem:pi0-grothendieck`) and the statement of the
Concentricity Theorem (master `thm:concentricity`).

The statement layer STOPS here: the proof of `thm:concentricity` — the
C1–C4 assembly, including the placement sentence (landed in the master
2026-07-03, the author's alone) — is Phase 4.

STATUS 2026-09-02 (synchronized to the analysis record, TASK-0004): this
file contains ZERO sorries.  The transitivity, connectedness, and
singleton-component results for the C-residue total are proved and clean.
The former universal theorem `ASection.concentricity` and the admitted
pairwise read equality it consumed were withdrawn: the universal statement is
false at this exact `ASection` type (Concentricity/SpecCandidate.lean).  The
clean interface that remains is at the end of this file; the zeta-specific
replacement surface is Concentricity/Corollaries.lean.
-/
import Concentricity.Toolkit
import Concentricity.ASectionCResidueDiagram
import Concentricity.ASectionTotalActionState
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.ConnectedComponents

set_option linter.style.header false

noncomputable section

open CategoryTheory

universe v u

/-- The connected-components functor π₀ : Cat ⥤ Type (master
`lem:pi0-grothendieck` proof: "The functor π₀ : Cat → Set is left adjoint to
the inclusion of discrete categories, so it preserves colimits; and
components of a category correspond one-to-one with components of its
classifying space (Quillen §1, SOURCES/Quillen73.md)"). Object part is
Mathlib's `ConnectedComponents`, morphism part `Functor.mapConnectedComponents`. -/
def pi0Functor : Cat.{v, u} ⥤ Type u where
  obj C := ConnectedComponents C
  map F := TypeCat.ofHom (Functor.mapConnectedComponents F.toFunctor)
  map_id C := by
    ext x
    refine Quotient.inductionOn x fun j => ?_
    simp
  map_comp F G := by
    ext x
    refine Quotient.inductionOn x fun j => ?_
    simp

section Pi0Grothendieck

variable {B : Type u} [SmallCategory B] (F : B ⥤ Grpd.{u, u})

/-- The canonical cocone of the component diagram π₀ ∘ F with apex
π₀(∫_𝓑 F): at b, a fibre component `mk x` goes to the total component
`mk ⟨b, x⟩` (the fibre inclusion `Grothendieck.ι`); naturality is the
zigzag along the hom `(f, 𝟙)` (`Grothendieck.ιNatTrans`). DERIVED (R10);
cocartesian register only (PHASE4_PLAN guardrail). -/
def pi0Cocone : Limits.Cocone ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) where
  pt := ConnectedComponents (Grothendieck (F ⋙ Grpd.forgetToCat))
  ι :=
    { app := fun b => TypeCat.ofHom
        (Functor.mapConnectedComponents (Grothendieck.ι (F ⋙ Grpd.forgetToCat) b))
      naturality := fun b b' f => by
        ext x
        refine _root_.Quotient.inductionOn x fun j => ?_
        simp only [pi0Functor, Functor.comp_obj, Functor.comp_map, types_comp_apply,
          TypeCat.ofHom_apply, Functor.mapConnectedComponents_mk,
          Functor.const_obj_obj, Functor.const_obj_map, types_id_apply]
        exact (_root_.Quotient.sound
          (Zigzag.of_hom ((Grothendieck.ιNatTrans f).app j))).symm }

/-- The object part of the comparison: a total object goes to the colimit
class of its fibre component over its base object. -/
def toColimitObj (X : Grothendieck (F ⋙ Grpd.forgetToCat)) :
    Limits.colimit ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) :=
  Limits.colimit.ι ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) X.base
    (CategoryTheory.ConnectedComponents.mk X.fiber)

/-- A morphism of ∫F leaves the comparison class unchanged: its base leg
is absorbed by the colimit identifications (`colimit.w`), its fibre leg by
the fibre's own π₀ (master `lem:pi0-grothendieck` proof: "zigzags project
to the base and join fibrewise"). -/
theorem toColimitObj_eq_of_hom {X Y : Grothendieck (F ⋙ Grpd.forgetToCat)}
    (φ : X ⟶ Y) : toColimitObj F X = toColimitObj F Y := by
  have h1 : toColimitObj F X
      = Limits.colimit.ι ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) Y.base
          (CategoryTheory.ConnectedComponents.mk
            (((F ⋙ Grpd.forgetToCat).map φ.base).toFunctor.obj X.fiber)) :=
    (Limits.colimit.w_apply ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) φ.base
      (CategoryTheory.ConnectedComponents.mk X.fiber)).symm
  have h2 := congrArg
    (fun t => Limits.colimit.ι ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) Y.base t)
    (_root_.Quotient.sound (Zigzag.of_hom φ.fiber))
  exact h1.trans h2

/-- Zigzag invariance of the comparison, by reflexive-transitive closure of
`toColimitObj_eq_of_hom`. -/
theorem toColimitObj_eq_of_zigzag {X Y : Grothendieck (F ⋙ Grpd.forgetToCat)}
    (h : Zigzag X Y) : toColimitObj F X = toColimitObj F Y := by
  induction h with
  | refl => rfl
  | tail _ hzag ih =>
    refine ih.trans ?_
    rcases hzag with hφ | hφ
    · exact toColimitObj_eq_of_hom F hφ.some
    · exact (toColimitObj_eq_of_hom F hφ.some).symm

/-- master `lem:pi0-grothendieck` as the named canonical equivalence:
π₀(∫_𝓑 F) ≃ colim_𝓑 (π₀ ∘ F). Forward: the comparison `toColimitObj`
descended along the π₀ quotient; inverse: `colimit.desc` of the canonical
cocone `pi0Cocone`; round trips by the Types colimit presentation
(`colimit.ι_desc`, `Types.jointly_surjective'`). Cocartesian register only
— no Quillen A / Thomason input (PHASE4_PLAN guardrail). -/
noncomputable def pi0GrothendieckEquiv :
    ConnectedComponents (Grothendieck (F ⋙ Grpd.forgetToCat))
      ≃ Limits.colimit ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) where
  toFun := _root_.Quotient.lift (toColimitObj F)
    fun _ _ h => toColimitObj_eq_of_zigzag F h
  invFun t := Limits.colimit.desc ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) (pi0Cocone F) t
  left_inv := _root_.Quotient.ind fun X =>
    (Limits.colimit.ι_desc_apply (pi0Cocone F) X.base
      (CategoryTheory.ConnectedComponents.mk X.fiber)).trans rfl
  right_inv t := by
    obtain ⟨b, y, rfl⟩ := Limits.Types.jointly_surjective' t
    refine _root_.Quotient.inductionOn y fun j => ?_
    have h1 := Limits.colimit.ι_desc_apply (pi0Cocone F) b
      (CategoryTheory.ConnectedComponents.mk j)
    calc _root_.Quotient.lift (toColimitObj F)
          (fun _ _ h => toColimitObj_eq_of_zigzag F h)
          (Limits.colimit.desc ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) (pi0Cocone F)
            (Limits.colimit.ι ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) b
              (CategoryTheory.ConnectedComponents.mk j)))
        = _root_.Quotient.lift (toColimitObj F)
            (fun _ _ h => toColimitObj_eq_of_zigzag F h)
            ((pi0Cocone F).ι.app b (CategoryTheory.ConnectedComponents.mk j)) :=
          congrArg (_root_.Quotient.lift (toColimitObj F)
            fun _ _ h => toColimitObj_eq_of_zigzag F h) h1
      _ = Limits.colimit.ι ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor) b
            (CategoryTheory.ConnectedComponents.mk j) := rfl

end Pi0Grothendieck

/-- master `lem:pi0-grothendieck` (verbatim): "For a functor F : 𝓑 → Grpd,
the connected-components functor carries the Grothendieck construction to
the colimit of the component diagram: π₀(∫_𝓑 F) ≅ colim_𝓑 (π₀ ∘ F)."
CLOSED by the named canonical equivalence `pi0GrothendieckEquiv` — the
master's proof is direct at the level of categories (zigzags project to
the base and join fibrewise); the classifying-space reading is Thomason
(SOURCES/Thomason79.md), expository, NOT used. -/
theorem pi0_grothendieck {B : Type u} [SmallCategory B] (F : B ⥤ Grpd.{u, u}) :
    Nonempty (ConnectedComponents (Grothendieck (F ⋙ Grpd.forgetToCat))
      ≃ Limits.colimit ((F ⋙ Grpd.forgetToCat) ⋙ pi0Functor)) :=
  ⟨pi0GrothendieckEquiv F⟩

/- RE-BADGED 2026-07-05 (PLAN_reencode §5), SUPERSEDED 2026-07-06 by the
author's ruling (a): the master label and endpoint now live on
`ASection.concentricity` below; this record is kept as the placement
paragraph's transcription map. Original text:
the endpoint, at its
translation-layer address; the remaining Lean transcription now lives on
`ASection.concentricity`, consumed by `cor:nontrivial`. Statement and
sorry unchanged.

**The placement** (master, proof of `thm:concentricity`, the placement
paragraph, verbatim): "Through the commuting triangle π∘E = exp
([Rem. 5.2(a)]{VS}), the unique tame lift traverses the logarithm manifold
as a single closed loop ([Cor. 5.13]{GPVwind}), and every point of the
degenerate fibre it meets is, by Lemma lem:exp-degenerate, the level log r
paired with an odd winding height I(2k+1)π: all multiplicity in the fibre
lies in the winding direction ([Cor. 5.21]{GPVwind}), none in the level.
Since 𝓑 is static — no morphisms between distinct levels (Definition
def:base) — the level is a conserved quantity along every zigzag of 𝒯_A,
and the degenerate fibre of the unique tame transport attached to the
A-section — the residue-ℂ zero-spheres {q_n} of C3 — lies over a *single*
level."

All four hypotheses are live in the assembly this transcribes (master,
assembly paragraph; R3): C2 supplies the outright continuation of the
hypercomplex logarithm on Ω₀ (`exists_log_continuation`); C3 the
exponential expression over the full divisor, agreeing with C2 on the
overlap by the Identity Theorem (`stem_identity`), whence the tame lift is
unique (`winding_lift_unique`); C1's pole is the cone through which the
value-loops close ([Cor. 5.13]{GPVwind}); C4 makes the degenerate fibre
infinite.

Queued (R8) — sorried against the sorried cone nodes of
Concentricity/Toolkit.lean; step-by-step transcription record:
(a) "the unique tame lift traverses the logarithm manifold as a single
closed loop" — GPVwind Cor 5.13, whose σ-apparatus is the recorded GAP of
`winding_loop_defect`; (b) "every point of the degenerate fibre it meets
is … the level log r paired with an odd winding height I(2k+1)π" —
`Octonion.exp_fibre_neg_real` (sorried); (c) the C2/C3 agreement feeding
(a) — `stem_identity` (sorried); (d) "the level is a conserved quantity
along every zigzag of 𝒯_A" — PROVED, `TotalObject.level_eq_of_zigzag`
(Concentricity/Base.lean); (e) "lies over a *single* level" — the
conclusion discharged here. -/
/- **THE CONCENTRICITY THEOREM** (master `thm:concentricity`; the
statement carrier per the author's ruling of 2026-07-06, superseding the
2026-07-05 re-encode: "(a) is literally the entire point of this entire
project" — the theorem, stated as the author means it): **the infinitely
many residue-ℂ zero-spheres of an A-section are concentric — one real
centre.** The concentric dictionary's reading of the A-section's one
concentric component: [the concentric component] → ∃ c, one centre.

THE ENDPOINT HAS TWO LEAN TRANSCRIPTION SEATS AND NO OUTSTANDING MATHEMATICAL
INFERENCE. Everything on both sides is proved and certified: the transport
connectivity (historically `concentricity_transport` — its file was
retired with the static tower; the live connectivity is the ι_A route
typed at this node), the
articulation (one component, defined through
the witness 𝔫, fibre concentric), the Φ-collapse and π₀(𝒮₂)
(PhiConversion.lean: the glue total and proper, the slice world's
components = the value moduli), the complete BL ladder (D0–D3 + mirror +
D2's proved kernel-coordinate iff (∃β two-sided positivity), the σ-closure rows, the
supplier chain, and the corollary chain (`cor:nontrivial`, `cor:rh` with
½ from `thm:rh-equiv`'s proved rigidity) consuming it downstream. The
transport's memory is the witness structure; the transport over the base
remembers the centres in the A-section (`rmk:collapse-cone`); this row is
the memory's readback. -/
/- THE PROOF PLAN OF RECORD (the author, 2026-07-07, verbatim — the argument
stated finally and completely; the transcription runs against exactly these
three clauses and nothing else:

1. A is a member of the ring 𝓡 of slice-preserving functions on the
   octonions, with properties C1–C4.
2. THAT IMPLIES THE GPV-BASE — which has everything: σ = c, unique winding,
   the *concentric* fibres and their connection.
3. The concentricity OF THE GPV BASE is EXTENDED to the concentricity of
   the infinitely many ℂ-residue spheres of the A-section, which land in a
   connected component.

The extension of clause 3 is the original extension move (the author,
from the first day): the concentric structure of the base extends along
the connection to the spheres. -/

-- CORRECTED 2026-07-26.  The previous comment here claimed
-- `ASection.concentricity` was "DECLARED AND PROVED in
-- ConcentricityReadout.lean".  It is not, and was not: that file declares
-- `ASection.SliceProjection.concentricityReadout`, whose conclusion is
-- `∃ κ : colimit (NaturalComponentDiagram A), ...` — a colimit point of the
-- retired slice projection, not a real part.  That whole file is quarantined.
--
-- `ASection.concentricity` (master `thm:concentricity`) is NOT YET DECLARED
-- anywhere in this repository.  It is the endgame target, and its name and
-- type are already fixed by its consumers in Corollaries.lean:
--
--   theorem ASection.concentricity (A : ASection) :
--       ∃ c : ℝ, ∀ n : ℕ, (A.sphereZero n).re = c
--
-- `ASection.nontrivial_one_centre` (Corollaries.lean:33) and
-- `zeta_riemannHypothesis` (:47) already called it at the time of this
-- record.  [Both were withdrawn on 2026-09-02; see SUPERSEDED below.]
--
-- It is declared at the end of the unified endgame ladder
-- (`register/70-whole-square.md` §7).  Per the ratified flight plan
-- (`register/80-concentricity-endgame.md`), it is declared HERE, at this
-- file's marked endpoint, against the three-clause proof plan of record
-- above.
--
-- SUPERSEDED 2026-09-02.  `ASection.concentricity` was declared here on
-- 2026-07-27 through one admitted pairwise read equality, and both were
-- withdrawn on 2026-09-02: the universal proposition is refuted by the
-- field-complete A-section `SpecCandidate.candidateSection`.  The consumers in
-- Corollaries.lean were rewritten to the zeta-specific equivalences.  See the
-- section "The readout boundary" at the end of this file.

/-- The certified membership of the enumerated representatives: every
`sphereZero m` is a member of the `ι_A`-included square at the north
frame, through the identity arrow (kernel-accepted; the dossier is
`sphereZero_mem_CResidueZeroLocus`). -/
theorem ASection.residueActionState_mem (A : ASection) (m : ℕ) :
    IsCResidueState A projectiveNorth
      (residueActionState A projectiveNorth m baseWorld) := by
  refine ⟨residueActionState A projectiveNorth m baseWorld,
    ?_, 𝟙 projectiveNorth, ?_⟩
  · show (residueActionState A projectiveNorth m
        baseWorld).positioned.back.coordinate ∈
      (fun z : ℂ => (z : OnePoint ℂ)) '' A.CResidueZeroLocus
    rw [residueActionState_positioned]
    exact ⟨A.sphereZero m, A.sphereZero_mem_CResidueZeroLocus m, rfl⟩
  · rw [AsectionActionTransport_id]
    rfl

/-- **A SUPPLIER, NOT THE RESULT** (badge corrected 2026-07-29, the author:
*"you misled us"*).  This quantifies over the **ambient** `H1`, not over the
C-residue system: it is `thm:G2-S6` re-spelled through the sweep, and it
says nothing about `ι_A`.  THE RESULT is that the A-section equivariant
functor — **part of the construction of `ι_A`**, its fibres being the
functor's graph (`AsectionStateInput ⋙ AsectionEquivariant =
AsectionStateOutput`, `rfl`) — is transitive on the C-residue system
`∫𝓡_A`, hence connected.  That is not this declaration.

The author's sentence this states one clause of, 2026-07-28 night: *"ι_A IS my
C-residue system and the equivariant A-section functor is transitive on it …
THE EQUIVARIANT A SECTION FUNCTOR IS LITERALLY TRANSITIVE ON THE IMAGINARY
OCTONIONS."*

`thm:G2-S6` **applied to the object**, not cited bare: on the imaginary
octonions where the members live, one element of `G₂` is one arrow of
`H1 = G₂ ⋉ 𝕆*` (`hom_as_subtype`, `Action.lean:92`), and
`AsectionEquivariant` carries that arrow — it *"retains the same `G₂`
element"* (`ASectionEquivariant.lean:49`), its naturality being
`realize_equivariant` itself. The element and the sweep together, applied to
the members. -/
theorem ASection.AsectionEquivariant_transitive (A : ASection) (p q : H1)
    {u v : Octonion} (hu : u ∈ Octonion.unitImaginarySphere)
    (hv : v ∈ Octonion.unitImaginarySphere)
    (hp : p.back = (u : OnePoint Octonion))
    (hq : q.back = (v : OnePoint Octonion)) :
    Nonempty ((A.AsectionEquivariant).obj p ⟶ (A.AsectionEquivariant).obj q) := by
  obtain ⟨g, hg⟩ := G2.exists_smul_eq_of_mem_unitImaginarySphere hu hv
  have harrow : p ⟶ q := ⟨g, by
    show g • p.back = q.back
    rw [hp, hq, ← hg]; rfl⟩
  exact ⟨(A.AsectionEquivariant).map harrow⟩

/-- **A SUPPLIER, NOT THE RESULT** (badge corrected 2026-07-29) — the same
clause read at the ambient states.  Like the declaration above it mentions
`ι_A` nowhere, and it is not the transitivity of the sweep on `∫𝓡_A`.

The anatomy it records — the same clause read where the
members live.  A member's input eye is `AsectionState.input s =
spherePt ↑s.world s.coordinate`: the point `σ + γ·v` of its own sphere, not
the bare direction.  `thm:G2-S6` is the transitivity of `G₂` on that sphere
(`lem:residue-spheres`: *"each such sphere `σ+γS⁶` is the `G₂`-orbit of any
of its points"*), and `AsectionStateInput` is a **functor**, so the arrow
travels through it — no coordinate law is needed on the way.  The sweep then
carries it, as in Declaration 0. -/
theorem ASection.AsectionEquivariant_transitive_states (A : ASection)
    (x y : A.AsectionStateWorld)
    (h : (CategoryTheory.ActionCategory.back x).coordinate
       = (CategoryTheory.ActionCategory.back y).coordinate) :
    Nonempty ((A.AsectionEquivariant).obj ((AsectionStateInput A).obj x) ⟶
              (A.AsectionEquivariant).obj ((AsectionStateInput A).obj y)) := by
  have key : ∀ s t : A.AsectionState, s.coordinate = t.coordinate →
      ∃ g : G2, g • s = t := by
    rintro ⟨sw, sc⟩ ⟨tw, tc⟩ hc
    obtain ⟨g, hg⟩ :=
      G2.exists_smul_eq_of_mem_unitImaginarySphere sw.2 tw.2
    refine ⟨g, ?_⟩
    simp only [HSMul.hSMul, SMul.smul, AsectionState.mk.injEq]
    exact ⟨Subtype.ext hg, hc⟩
  obtain ⟨g, hg⟩ := key _ _ h
  exact ⟨(A.AsectionEquivariant).map ((AsectionStateInput A).map (⟨g, hg⟩ : x ⟶ y))⟩

/-- **DECLARATION 1** (the author's, verbatim, `def:residue-subdiagram`):
`ι_A : 𝓡_A ⇒ 𝓐_A` is "a faithful embedding onto its image, and its
naturality squares commute definitionally."

Wiring only: `(AsectionCResidueInclusion A).app X` **is**
`(IsCResidueState A X).ι` (`ASectionCResidueDiagram.lean:165`), and `𝓡_A`
**is** its own image (`FullSubcategory`; `ι_obj` = `rfl`).  Mathlib carries
the fact — `fullyFaithfulι` on `[propext]` alone — but resolution matches
surface syntax, so it fires on the `ι` spelling and not on `ι_A`'s name.
These declarations put it under the author's name. -/
def ASection.AsectionCResidueInclusion_app_fullyFaithful
    (A : ASection) (X : GreatCircle.Base) :
    ((AsectionCResidueInclusion A).app X).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance ASection.AsectionCResidueInclusion_app_full
    (A : ASection) (X : GreatCircle.Base) :
    ((AsectionCResidueInclusion A).app X).Full :=
  ObjectProperty.full_ι _

instance ASection.AsectionCResidueInclusion_app_faithful
    (A : ASection) (X : GreatCircle.Base) :
    ((AsectionCResidueInclusion A).app X).Faithful :=
  ObjectProperty.faithful_ι _

/-- **`𝒯_A`** — the total value-transport category of master `def:base`,
`𝒯_A = ∫_𝓑 𝓐_A`.  Named here because it had none: it was written inline
wherever it occurred, so no declaration could be stated *at* it. -/
abbrev ASection.ambientTotalCategory (A : ASection) : Type :=
  Grothendieck (A.AsectionActionDiagram ⋙ Grpd.forgetToCat)

/-- The earlier projective-frame presentation, retained for the already-built
componentwise inclusion certificates below. -/
abbrev ASection.projectiveResidueTotalCategory (A : ASection) : Type :=
  Grothendieck (A.AsectionCResidueDiagram ⋙ Grpd.forgetToCat)

/-- The C-residue total over its actual semantic inverse-image input-groupoid
locus. -/
abbrev ASection.residueTotalCategory (A : ASection) : Type :=
  A.CResidueInputTotalCategory

/-- **`ι_A` AT THE TOTAL** (the author, 2026-07-29): *"it is a natural
transformation OF THE TOTAL GROTHENDIECK CONSTRUCTION — an inverse image OF
the total `F_A(X)`."*  This is that reading in Lean: the inclusion of the
inverse image `∫𝓡_A` in the total `T_A`.  *"`∫𝓡_A` isn't parallel to `T_A`,
it is INSIDE IT."* -/
noncomputable def ASection.AsectionCResidueInclusionTotal (A : ASection) :
    A.projectiveResidueTotalCategory ⥤
    A.ambientTotalCategory :=
  Grothendieck.map
    (Functor.whiskerRight (AsectionCResidueInclusion A) Grpd.forgetToCat)

/-- `ι_A` is FAITHFUL AT THE TOTAL.  Mathlib has no lemma that
`Grothendieck.map` of a fully faithful transformation is fully faithful
(`Grothendieck.lean` carries `map` `:242`, `map_map` `:262`, and
`faithful_ι` `:560` for the *fibre* inclusion, and nothing else) — so the
total-level head was an empty shelf, exactly as `ι_A`'s componentwise head
was before `bb02b54`.  This puts it under a name.  Consumes Declaration 1
at `ι_A`'s own name; the structural work is `Grothendieck.ext` (`:93`). -/
instance ASection.AsectionCResidueInclusionTotal_faithful (A : ASection) :
    (AsectionCResidueInclusionTotal A).Faithful where
  map_injective {P Q} f g h := by
    obtain ⟨fb, ff⟩ := f
    obtain ⟨gb, gf⟩ := g
    simp only [AsectionCResidueInclusionTotal, Grothendieck.map] at h
    injection h with hb hf
    subst hb
    refine Grothendieck.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    have h2 := eq_of_heq hf
    simp at h2
    exact (AsectionCResidueInclusion_app_faithful A Q.base).map_injective h2

/-- `ι_A` is FULL AT THE TOTAL — so, with faithfulness above, the inclusion
of the inverse image in the total is an isomorphism onto its image.  This is
the author's *"a transitive action groupoid whose fully faithful image is
`∫𝓡_A`"*, stated where he says it lives: at the total. -/
instance ASection.AsectionCResidueInclusionTotal_full (A : ASection) :
    (AsectionCResidueInclusionTotal A).Full where
  map_surjective {P Q} φ := by
    haveI := AsectionCResidueInclusion_app_full A Q.base
    refine ⟨⟨φ.base,
      ((AsectionCResidueInclusion A).app Q.base).preimage φ.fiber⟩, ?_⟩
    refine Grothendieck.ext _ _ rfl ?_
    simp only [AsectionCResidueInclusionTotal, Grothendieck.map, eqToHom_refl]
    erw [Functor.map_preimage]
    show 𝟙 _ ≫ 𝟙 _ ≫ φ.fiber = φ.fiber
    simp

/-- Once the A-specific north transport has matched the stored input
coordinate, the already-built `G₂` action supplies exactly the remaining
sphere-direction morphism. -/
theorem ASection.northFiberHom_of_coordinate
    (A : ASection)
    (xN yN : AsectionActionFiber A projectiveNorth)
    (k : projectiveNorth ⟶ projectiveNorth)
    (hcoordinate :
      (((AsectionActionTransport A k).obj xN).input.back.coordinate) =
        yN.input.back.coordinate) :
    Nonempty ((AsectionActionTransport A k).obj xN ⟶ yN) := by
  let tx := (AsectionActionTransport A k).obj xN
  have key : ∀ s t : AsectionState A, s.coordinate = t.coordinate →
      ∃ g : G2, g • s = t := by
    rintro ⟨sw, sc⟩ ⟨tw, tc⟩ hc
    obtain ⟨g, hg⟩ :=
      G2.exists_smul_eq_of_mem_unitImaginarySphere sw.2 tw.2
    refine ⟨g, ?_⟩
    simp only [HSMul.hSMul, SMul.smul, AsectionState.mk.injEq]
    exact ⟨Subtype.ext hg, hc⟩
  obtain ⟨g₂, hstate⟩ := key tx.input.back yN.input.back hcoordinate
  exact ⟨InducedCategory.homMk
    (show tx.input ⟶ yN.input from ⟨g₂, hstate⟩)⟩

/-- Inversion sends a stabilizer part to its inverse (master `lem:c-residue-
transitive`, (R)).  Inversion of the residual factor, stated on its own. -/
theorem ASection.stabilizerPart_inv {X Y : GreatCircle.Base} (k : X ⟶ Y) :
    GreatCircle.stabilizerPart (CategoryTheory.Groupoid.inv k)
      = (GreatCircle.stabilizerPart k)⁻¹ := by
  have hmul :
      GreatCircle.stabilizerPart k *
          GreatCircle.stabilizerPart (CategoryTheory.Groupoid.inv k) = 1 := by
    calc
      GreatCircle.stabilizerPart k *
            GreatCircle.stabilizerPart (CategoryTheory.Groupoid.inv k) =
          GreatCircle.stabilizerPart (CategoryTheory.Groupoid.inv k ≫ k) :=
        (GreatCircle.stabilizerPart_comp (CategoryTheory.Groupoid.inv k) k).symm
      _ = GreatCircle.stabilizerPart (𝟙 Y) :=
        congrArg GreatCircle.stabilizerPart (CategoryTheory.Groupoid.inv_comp k)
      _ = 1 := GreatCircle.stabilizerPart_id Y
  exact eq_inv_of_mul_eq_one_right hmul

/-- The Cayley reading of the same fact; `cayleyProjective` is a monoid map. -/
theorem ASection.cayleyProjective_stabilizerPart_inv {X Y : GreatCircle.Base}
    (k : X ⟶ Y) :
    (GreatCircle.cayleyProjective (GreatCircle.stabilizerPart k).1)⁻¹
      = GreatCircle.cayleyProjective
          (GreatCircle.stabilizerPart (CategoryTheory.Groupoid.inv k)).1 := by
  rw [ASection.stabilizerPart_inv k, Subgroup.coe_inv, map_inv]

/-- Reversing a boundary square is the square of the reversed base arrow. -/
theorem ASection.orbitStabilizerActionSquare_inv (A : ASection)
    {X Y : GreatCircle.Base} (k : X ⟶ Y) :
    (A.orbitStabilizerActionSquare k).inv
      = A.orbitStabilizerActionSquare (CategoryTheory.Groupoid.inv k) := by
  apply ASection.ActionTransportSquare.ext <;>
    simp [ASection.orbitStabilizerActionSquare,
      ASection.ActionTransportSquare.inv, ASection.projectiveArrowElement,
      ASection.cayleyProjective_stabilizerPart_inv k, mul_assoc]

/-- **The boundary face of a forced residual factor** (master
`lem:c-residue-transitive`).  Orbit--stabilizer gives `k_• = o_N r_• o_0⁻¹`,
and at the north frame `o_N = 1`.  So a boundary face out of the common
projective zero frame is built FROM its residual stabilizer part, rather than
searched for: the factorization is the constructor. -/
def ASection.faceOfStabilizerPart (r : GreatCircle.NorthStabilizer) :
    GreatCircle.pointObj ((0 : ℝ) : GreatCircle.Point) ⟶ ASection.projectiveNorth :=
  ⟨r.1 * (GreatCircle.orbitRep ((0 : ℝ) : GreatCircle.Point))⁻¹, by
    have h0 : (GreatCircle.orbitRep ((0 : ℝ) : GreatCircle.Point))⁻¹ •
        (((0 : ℝ) : GreatCircle.Point)) = (OnePoint.infty : GreatCircle.Point) := by
      rw [inv_smul_eq_iff]
      exact (GreatCircle.orbitRep_spec ((0 : ℝ) : GreatCircle.Point)).symm
    change (r.1 * (GreatCircle.orbitRep ((0 : ℝ) : GreatCircle.Point))⁻¹) •
      (((0 : ℝ) : GreatCircle.Point)) = (OnePoint.infty : GreatCircle.Point)
    rw [mul_smul, h0]
    exact r.2⟩

/-- `stabilizerPart_unique` identifies that face's residual factor as exactly
the one it was built from — the uniqueness half of master (R). -/
theorem ASection.stabilizerPart_faceOfStabilizerPart
    (r : GreatCircle.NorthStabilizer) :
    GreatCircle.stabilizerPart (ASection.faceOfStabilizerPart r) = r :=
  (GreatCircle.stabilizerPart_unique _ r (by
    show r.1 * (GreatCircle.orbitRep ((0 : ℝ) : GreatCircle.Point))⁻¹ = _
    rw [show (CategoryTheory.ActionCategory.back ASection.projectiveNorth)
          = (OnePoint.infty : GreatCircle.Point) from rfl,
        GreatCircle.orbitRep_infty, one_mul]
    rfl)).symm

/-- **(S)+(B) ⟹ (I)** (master `lem:c-residue-transitive`).  A boundary face is
a commuting action square: its `commutes` field *is* the square identity
`L S = D R`.  Evaluating that at the common input `u_*` of the fixed tape and
using the C3 boundary reading `L (S u_*) = D u`, cancellation by the Möbius
automorphism `D` yields the input equation `R u_* = u` — where `R` is the Cayley
action of the uniquely determined stabilizer part. -/
theorem ASection.inputEquation_of_boundaryReading
    {S D : ↥Moebius} (sq : ASection.ActionTransportSquare S D)
    (uStar u : OnePoint ℂ)
    (hB : sq.left.val (S.val uStar) = D.val u) :
    sq.right.val uStar = u := by
  have h2 : sq.left.val (S.val uStar) = D.val (sq.right.val uStar) := by
    have h1 : (sq.left * S).val uStar = (D * sq.right).val uStar := by
      rw [sq.commutes]
    exact h1
  rw [hB] at h2
  exact ((EquivLike.apply_eq_iff_eq (D : OnePoint ℂ ≃ OnePoint ℂ)).mp h2).symm

/-- **(Φ) FROM THE TWO C3 BOUNDARY READINGS** (master
`lem:c-residue-transitive`, the comparison).  Two runs `k₁, k₂` of the one
construction out of the one source object, read at its one input `u_*`.  Their
C3 boundary readings land the positioned outputs on the authored coordinates —
`hB₁`, `hB₂` state that against `D_A` itself, since the north frame **is** `D_A`
(`projectiveObjectFrame_north`), and `residueState_graph` is what says the
right-hand sides are `sphereZero n`, `sphereZero m`.  Then:

  (S)+(B)+(P) ⟹ (I)   `inputEquation_of_boundaryReading`, once per run
  (R)                 `stabilizerPart_comp`, `stabilizerPart_inv`
  (Φ)                 `northFiberHom_of_coordinate`, `G₂` on the direction

The residual factors are `stabilizerPart` of the two runs — determined by the
orbit--stabilizer factorization, never quantified over. -/
theorem ASection.northComparison_of_boundaryReadings
    (A : ASection) {X : GreatCircle.Base}
    (k₁ k₂ : X ⟶ ASection.projectiveNorth)
    (xN yN : A.AsectionActionFiber ASection.projectiveNorth)
    (uStar : OnePoint ℂ)
    (hB₁ : (A.orbitStabilizerActionSquare k₁).left.val
              ((A.projectiveObjectFrame X).val uStar)
            = (A.distinguishedDiskAction).val xN.input.back.coordinate)
    (hB₂ : (A.orbitStabilizerActionSquare k₂).left.val
              ((A.projectiveObjectFrame X).val uStar)
            = (A.distinguishedDiskAction).val yN.input.back.coordinate) :
    Nonempty ((A.AsectionActionTransport
      (CategoryTheory.Groupoid.inv k₁ ≫ k₂)).obj xN ⟶ yN) := by
  rw [← ASection.projectiveObjectFrame_north A] at hB₁ hB₂
  have hI₁ : (GreatCircle.cayleyProjective
      (GreatCircle.stabilizerPart k₁).1).val uStar
      = xN.input.back.coordinate :=
    ASection.inputEquation_of_boundaryReading
      (A.orbitStabilizerActionSquare k₁) uStar _ hB₁
  have hI₂ : (GreatCircle.cayleyProjective
      (GreatCircle.stabilizerPart k₂).1).val uStar
      = yN.input.back.coordinate :=
    ASection.inputEquation_of_boundaryReading
      (A.orbitStabilizerActionSquare k₂) uStar _ hB₂
  refine A.northFiberHom_of_coordinate _ _ _ ?_
  rw [ASection.AsectionActionTransport_obj_input]
  change
    (GreatCircle.cayleyProjective
      (GreatCircle.stabilizerPart
        (CategoryTheory.Groupoid.inv k₁ ≫ k₂)).1).val
          xN.input.back.coordinate =
      yN.input.back.coordinate
  rw [GreatCircle.stabilizerPart_comp, ASection.stabilizerPart_inv,
      Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, ← hI₁]
  simpa using hI₂

/-- **(R)** (master `lem:c-residue-transitive`): the relative base arrow's
transport is the endosquare's transport — the inverse Euler square followed by
the Weierstrass square, read on the A-generated value states.  The two boundary
presentations are parallel squares `S ⟶ D` with `D = A.distinguishedDiskAction`
by `projectiveObjectFrame_north`. -/
theorem ASection.relativeSquare_transport (A : ASection)
    {X Y Z : GreatCircle.Base} (kE : X ⟶ Y) (kW : X ⟶ Z) :
    A.AsectionActionTransport (CategoryTheory.Groupoid.inv kE ≫ kW)
      = ((A.orbitStabilizerActionSquare kE).inv.comp
          (A.orbitStabilizerActionSquare kW)).actionStateTransport A := by
  rw [ASection.ActionTransportSquare.actionStateTransport_comp,
      A.AsectionActionTransport_comp]
  congr 1
  · rw [ASection.orbitStabilizerActionSquare_inv]
    rfl

/-- **MASTER (P), READ OFF — nothing derived.**  The inverse-image groupoid
`𝓡_A(N)` supplies the inputs occurring in the graph (A).  Its residue
condition *identifies* the state's positioned entry with an authored C3
coordinate `z`, and the graph equation `positioned = D·input` is a field of
the state itself (`positioned_by_action`); at the north object `o_N = 1`, so
the positioned frame **is** `D_A` (`projectiveObjectFrame_north`).  Reading
those off together:

    D_A(u) = z,      z ∈ CResidueZeroLocus = {z | A.F z = 0 ∧ 0 < z.im}.

So `u = D_A⁻¹(z)` is the canonical preimage of a selected residue state — the
input is never chosen, and `0 < z.im` (off the `G₂`-fixed great circle) comes
with the selection rather than as a hypothesis. -/
theorem ASection.residueState_graph (A : ASection)
    (zN : A.AsectionActionFiber ASection.projectiveNorth)
    (hzN : ASection.IsNorthCResidueState A zN) :
    ∃ n : ℕ,
      (A.distinguishedDiskAction).val
          (CategoryTheory.ActionCategory.back zN.input).coordinate
            = ((A.sphereZero n : ℂ) : OnePoint ℂ) := by
  obtain ⟨z, hz, hzc⟩ := hzN
  obtain ⟨n, hn⟩ := (A.mem_CResidueZeroLocus_iff_exists_sphereZero z).mp hz
  refine ⟨n, ?_⟩
  rw [hn]
  have hzc' : (z : OnePoint ℂ)
      = (CategoryTheory.ActionCategory.back zN.positioned).coordinate := hzc
  have h2 : (CategoryTheory.ActionCategory.back zN.positioned).coordinate
      = (A.projectiveObjectFrame ASection.projectiveNorth).val
          (CategoryTheory.ActionCategory.back zN.input).coordinate := by
    rw [zN.positioned_by_action]
    exact coordinateTransport_obj_coordinate A _ _
  rw [hzc'.trans h2]
  exact congrArg
    (fun m : Moebius => m.val
      (CategoryTheory.ActionCategory.back zN.input).coordinate)
    (projectiveObjectFrame_north A).symm

/-- **THE TOTALS ARE GROUPOIDS — the classification.**  Grothendieck of a
`Grpd`-valued functor over a groupoid base is a groupoid: every morphism is
invertible, its base leg by the base's groupoid structure, its fibre leg by the
fibre's, and `Grothendieck.isoMk` assembles the two into an isomorphism of the
total.  Nothing is hand-rolled — no inverse is built out of `Grothendieck.Hom`.

This is the shelf Mathlib leaves empty: `Grothendieck.isoMk` and
`Groupoid.ofIsIso` both exist and were never composed.  Stated once and
instantiated at the author's two totals below, it is what makes
"a transitive action groupoid is connected"
(`Mathlib/CategoryTheory/Action.lean:128`) available at `∫𝓡_A`. -/
noncomputable instance grothendieckGrpdGroupoid
    {C : Type*} [CategoryTheory.Groupoid C] (F : C ⥤ Grpd) :
    CategoryTheory.Groupoid (Grothendieck (F ⋙ Grpd.forgetToCat)) :=
  CategoryTheory.Groupoid.ofIsIso (fun {X Y} f => by
    letI gY : CategoryTheory.Groupoid ((F ⋙ Grpd.forgetToCat).obj Y.base) :=
      (F.obj Y.base).str
    haveI hb : CategoryTheory.IsIso f.base :=
      ⟨CategoryTheory.Groupoid.inv f.base,
        CategoryTheory.Groupoid.comp_inv f.base,
        CategoryTheory.Groupoid.inv_comp f.base⟩
    letI hf : CategoryTheory.IsIso f.fiber :=
      ⟨@CategoryTheory.Groupoid.inv _ gY _ _ f.fiber,
       @CategoryTheory.Groupoid.comp_inv _ gY _ _ f.fiber,
       @CategoryTheory.Groupoid.inv_comp _ gY _ _ f.fiber⟩
    have h : (CategoryTheory.Grothendieck.isoMk
        (CategoryTheory.asIso f.base)
        (@CategoryTheory.asIso _ _ _ _ f.fiber hf)).hom = f := rfl
    rw [← h]
    infer_instance)

/-- `𝒯_A` is an action groupoid: the classification instantiated at the
ambient total. -/
noncomputable instance ASection.ambientTotalGroupoid (A : ASection) :
    CategoryTheory.Groupoid A.ambientTotalCategory :=
  grothendieckGrpdGroupoid A.AsectionActionDiagram

/-- `∫𝓡_A` is a groupoid: the same classification at the C-residue total, the
sub-action-groupoid `ι_A` includes fully and faithfully. -/
noncomputable instance ASection.residueTotalGroupoid (A : ASection) :
    CategoryTheory.Groupoid A.residueTotalCategory :=
  grothendieckGrpdGroupoid A.AsectionCResidueInputDiagram

/-- **STEP 2 OF THE ACTION-GROUPOID ARGUMENT, master (P).**  A north
C-residue state IS the enumerated residue action state at its own zero index
and its own direction.  Positioned determines input (`D_A` invertible,
`coordinateTransport_mul`), input determines the state (`ofInput`), so this is
read off the state and nothing is constructed.  Imported from the certified
receipt `northState_is_residueActionState_audit`. -/
theorem ASection.northState_is_residueActionState
    (A : ASection) (zN : AsectionActionFiber A projectiveNorth)
    (hzN : IsNorthCResidueState A zN) :
    ∃ n : ℕ, ∃ I : SphereWorld,
      zN = residueActionState A projectiveNorth n I := by
  obtain ⟨z, hz, hzcoord⟩ := hzN
  obtain ⟨n, hn⟩ :=
    (A.mem_CResidueZeroLocus_iff_exists_sphereZero z).mp hz
  let I : SphereWorld := zN.positioned.back.world
  refine ⟨n, I, ?_⟩
  have hpositioned_world :
      zN.positioned.back.world = I := rfl
  have hpositioned_coordinate :
      zN.positioned.back.coordinate =
        (A.sphereZero n : OnePoint ℂ) :=
    hzcoord.symm.trans
      (congrArg (fun w : ℂ => (w : OnePoint ℂ)) hn).symm
  have hpositioned :
      zN.positioned =
        ((A.residueState n I : AsectionState A) :
          AsectionStateWorld A) := by
    have state_eq :
        ∀ s t : AsectionState A,
          s.world = t.world →
          s.coordinate = t.coordinate →
          s = t := by
      rintro ⟨sw, sc⟩ ⟨tw, tc⟩ hw hc
      cases hw
      cases hc
      rfl
    rw [← CategoryTheory.ActionCategory.back_coe zN.positioned]
    apply congrArg
    exact state_eq _ _ hpositioned_world hpositioned_coordinate
  have hinput :
      zN.input =
        (coordinateTransport A
          (projectiveObjectFrame A projectiveNorth)⁻¹).obj
            ((A.residueState n I : AsectionState A) :
              AsectionStateWorld A) := by
    have hgraph := zN.positioned_by_action
    rw [hpositioned] at hgraph
    have hinv := congrArg
      (fun y => (coordinateTransport A
        (projectiveObjectFrame A projectiveNorth)⁻¹).obj y) hgraph
    calc
      zN.input =
          (coordinateTransport A
            (projectiveObjectFrame A projectiveNorth)⁻¹).obj
              ((coordinateTransport A
                (projectiveObjectFrame A projectiveNorth)).obj
                  zN.input) := by
            change zN.input =
              ((coordinateTransport A
                (projectiveObjectFrame A projectiveNorth) ⋙
                coordinateTransport A
                  (projectiveObjectFrame A projectiveNorth)⁻¹).obj
                    zN.input)
            rw [coordinateTransport_mul]
            simp [coordinateTransport_one]
      _ = (coordinateTransport A
            (projectiveObjectFrame A projectiveNorth)⁻¹).obj
              ((A.residueState n I : AsectionState A) :
                AsectionStateWorld A) := hinv.symm
  apply AsectionActionState.ext
  · exact hinput
  · simpa only [residueActionState_positioned] using hpositioned
  · rw [zN.value_realized,
      (residueActionState A projectiveNorth n I).value_realized,
      residueActionState_positioned, hpositioned]

/-- **THE INPUT IS $D_A^{-1}(z_n)$, computed.**  Master (P): the enumerated
residue action state's stored input coordinate is the canonical preimage of
the `n`-th C3 zero under the distinguished disk action.  Imported from the
certified receipt `residueActionState_north_input_audit`. -/
theorem ASection.residueActionState_north_input
    (A : ASection) (n : ℕ) (I : SphereWorld) :
    (residueActionState A projectiveNorth n I).input.back.coordinate =
      (A.distinguishedDiskAction⁻¹).val
        (A.sphereZero n : OnePoint ℂ) := by
  simp [residueActionState, AsectionActionState.ofInput,
    residueState, projectiveNorth, projectiveObjectFrame_north]

/-- **THE TRANSPORTED INPUT** (master `lem:c-residue-transitive`).  A north
loop acts on the stored input by the Cayley action of its stabilizer part.
Imported from the certified receipt `residueActionTransport_north_input_audit`. -/
theorem ASection.residueActionTransport_north_input
    (A : ASection) (n : ℕ) (I : SphereWorld)
    (k : projectiveNorth ⟶ projectiveNorth) :
    (((AsectionActionTransport A k).obj
        (residueActionState A projectiveNorth n I)).input.back.coordinate) =
      (GreatCircle.cayleyProjective
        (GreatCircle.stabilizerPart k).1).val
          ((A.distinguishedDiskAction⁻¹).val
            (A.sphereZero n : OnePoint ℂ)) := by
  rw [AsectionActionTransport_obj_input]
  simp [orbitStabilizerActionSquare, residueActionState,
    AsectionActionState.ofInput, residueState, projectiveNorth,
    projectiveObjectFrame_north]

/-- **THE SLICE-WORLD REGISTER.**  A sphere morphism already carries its
Möbius stem; no projective element is chosen here.  Imported from the
certified receipt `sphereWorld_relative_stem_audit`. -/
theorem ASection.sphereWorld_relative_stem
    {I J : SphereWorld} (E W : I ⟶ J) :
    (CategoryTheory.Groupoid.inv E ≫ W).mob =
      W.mob * E.mob⁻¹ := rfl

/-- The north-pole A-action conjugates that stem by the distinguished disk
action.  Imported from `northPoleAction_relative_stem_audit`. -/
theorem ASection.northPoleAction_relative_stem
    (A : ASection) {I J : SphereWorld} (E W : I ⟶ J) :
    ((northPoleAction A).map
      (CategoryTheory.Groupoid.inv E ≫ W)).mob =
        A.distinguishedDiskAction *
          (W.mob * E.mob⁻¹) *
            A.distinguishedDiskAction⁻¹ := rfl

/-- **(I) IN THE SLICE-WORLD REGISTER.**  The relative stem carries the first
reading to the second — the master's input equations, read where the morphism
carries its own stem.  Imported from `sphereWorld_relative_stem_maps_audit`. -/
theorem ASection.sphereWorld_relative_stem_maps
    {I J : SphereWorld} (E W : I ⟶ J)
    (uStar uE uW : OnePoint ℂ)
    (hE : E.mob.val uStar = uE)
    (hW : W.mob.val uStar = uW) :
    (CategoryTheory.Groupoid.inv E ≫ W).mob.val uE = uW := by
  rw [sphereWorld_relative_stem, ← hE]
  simpa using hW

/-- The same relative stem as a composite of distinguished world actions.
Imported from `sphereWorld_relative_functor_audit`. -/
theorem ASection.sphereWorld_relative_functor
    {I J : SphereWorld} (E W : I ⟶ J) :
    distinguishedWorldAction E.mob⁻¹ ⋙
        distinguishedWorldAction W.mob =
      distinguishedWorldAction (W.mob * E.mob⁻¹) :=
  distinguishedWorldAction_comp E.mob⁻¹ W.mob

/-- **THE ROUND-TRIP PACKAGING.**  Euler and Weierstrass are parallel
two-legged action squares; reversing the Euler square and composing the
Weierstrass square produces an endosquare of their common target, whose two
stems are the relative Möbius elements.  Imported from
`relativeActionSquare_left_audit` / `_right_audit`. -/
theorem ASection.relativeActionSquare_left
    {source target : Moebius}
    (E W : ASection.ActionTransportSquare source target) :
    (E.inv.comp W).left = W.left * E.left⁻¹ := rfl

theorem ASection.relativeActionSquare_right
    {source target : Moebius}
    (E W : ASection.ActionTransportSquare source target) :
    (E.inv.comp W).right = W.right * E.right⁻¹ := rfl

/-- The endosquare's action-state transport is the composite supplied by the
round trip.  Imported from `relativeActionSquare_transport_audit`. -/
theorem ASection.relativeActionSquare_transport
    (A : ASection) {source target : Moebius}
    (E W : ASection.ActionTransportSquare source target) :
    (E.inv.comp W).actionStateTransport A =
      E.inv.actionStateTransport A ⋙ W.actionStateTransport A :=
  ASection.ActionTransportSquare.actionStateTransport_comp A E.inv W

/-- **(N)/(G) — THE MORPHISM.**  Given a north comparison `(k, φ)`, functorial
transport along `(g⁻¹ ≫ k) ≫ h` carries it to arbitrary `P, Q`, and fullness
returns it to `∫𝓡_A`.  This is the master's closing paragraph.  Imported from
the certified receipt `residueTotal_morphism_of_northComparison_audit`. -/
theorem ASection.residueTotal_morphism_of_northComparison
    (A : ASection)
    (P Q : Grothendieck
      (AsectionCResidueDiagram A ⋙ Grpd.forgetToCat))
    (xN yN : AsectionActionFiber A projectiveNorth)
    (g : projectiveNorth ⟶ P.base)
    (hg : (AsectionActionTransport A g).obj xN = P.fiber.obj)
    (h : projectiveNorth ⟶ Q.base)
    (hh : (AsectionActionTransport A h).obj yN = Q.fiber.obj)
    (k : projectiveNorth ⟶ projectiveNorth)
    (φ : (AsectionActionTransport A k).obj xN ⟶ yN) :
    Nonempty (P ⟶ Q) := by
  let inclusion := AsectionCResidueInclusionTotal A
  have hback : (AsectionActionTransport A
      (CategoryTheory.Groupoid.inv g)).obj P.fiber.obj = xN := by
    calc
      (AsectionActionTransport A
          (CategoryTheory.Groupoid.inv g)).obj P.fiber.obj =
          (AsectionActionTransport A
            (CategoryTheory.Groupoid.inv g)).obj
              ((AsectionActionTransport A g).obj xN) := by rw [hg]
      _ = (AsectionActionTransport A
            (g ≫ CategoryTheory.Groupoid.inv g)).obj xN :=
          (congrArg (fun F => F.obj xN)
            (AsectionActionTransport_comp A g
              (CategoryTheory.Groupoid.inv g))).symm
      _ = xN := by
        have harrow : g ≫ CategoryTheory.Groupoid.inv g =
            𝟙 projectiveNorth := CategoryTheory.Groupoid.comp_inv g
        rw [harrow, AsectionActionTransport_id]
        rfl
  have hsrc : (AsectionActionTransport A
      ((CategoryTheory.Groupoid.inv g ≫ k) ≫ h)).obj P.fiber.obj =
      (AsectionActionTransport A h).obj
        ((AsectionActionTransport A k).obj xN) := by
    calc
      (AsectionActionTransport A
          ((CategoryTheory.Groupoid.inv g ≫ k) ≫ h)).obj P.fiber.obj =
          (AsectionActionTransport A h).obj
            ((AsectionActionTransport A
              (CategoryTheory.Groupoid.inv g ≫ k)).obj P.fiber.obj) :=
        congrArg (fun F => F.obj P.fiber.obj)
          (AsectionActionTransport_comp A
            (CategoryTheory.Groupoid.inv g ≫ k) h)
      _ = (AsectionActionTransport A h).obj
            ((AsectionActionTransport A k).obj
              ((AsectionActionTransport A
                (CategoryTheory.Groupoid.inv g)).obj P.fiber.obj)) := by
          rw [AsectionActionTransport_comp]
          rfl
      _ = (AsectionActionTransport A h).obj
            ((AsectionActionTransport A k).obj xN) := by rw [hback]
  have ambientφ : inclusion.obj P ⟶ inclusion.obj Q := by
    refine ⟨(CategoryTheory.Groupoid.inv g ≫ k) ≫ h, ?_⟩
    exact eqToHom hsrc ≫
      (AsectionActionTransport A h).map φ ≫
      eqToHom hh
  exact ⟨inclusion.preimage ambientφ⟩

/-- **CONNECTED FROM TRANSITIVE**, on this exact C-residue total — not a
generic category.  C4 supplies nonemptiness.  Imported from the certified
receipt `residueTotal_isConnected_of_transitive_audit`. -/
theorem ASection.residueTotal_isConnected_of_transitive
    (A : ASection)
    (htrans : ∀ P Q : A.residueTotalCategory,
      Nonempty (P ⟶ Q)) :
    CategoryTheory.IsConnected A.residueTotalCategory := by
  haveI : Nonempty A.residueTotalCategory :=
    ⟨A.residueInputTotalObject 0 baseWorld⟩
  exact zigzag_isConnected fun P Q =>
    CategoryTheory.Zigzag.of_hom (htrans P Q).some

/-- **π₀ SINGLETON FROM CONNECTED** (CHT Remark 8.3.5), on this exact total.
Imported from `residueTotal_pi0_singleton_of_connected_audit`. -/
theorem ASection.residueTotal_pi0_singleton_of_connected
    (A : ASection)
    [CategoryTheory.IsConnected A.residueTotalCategory] :
    ∀ P Q : A.residueTotalCategory,
      CategoryTheory.ConnectedComponents.mk P =
        CategoryTheory.ConnectedComponents.mk Q :=
  fun P Q => _root_.Quotient.sound (CategoryTheory.isPreconnected_zigzag P Q)

/-- **THE RESULT** — Two arbitrary members of the C-residue system are connected
by a morphism of `∫𝓡_A`.  Their stored input coordinates are arbitrary objects
of the semantic C-residue inverse-image groupoid locus.  Its base arrow moves
the first input to the second; the one existing disk action transports that
arrow, with its winding already inside `D_A`; then `G₂` supplies the remaining
direction morphism in the target fibre.  No equality of the two input
coordinates and no identity north transport is asserted. -/
theorem ASection.sweepTransitive_on_residueSystem (A : ASection) :
    ∀ P Q : A.residueTotalCategory,
      Nonempty (P ⟶ Q) := by
  exact A.CResidueInputTotal_transitive

/-- **DECLARATION 2** (the author's, verbatim): `∫𝓡_A` — `ι_A`'s total —
IS CONNECTED, immediately, because `ι_A` is a *proper* inclusion and a
natural isomorphism onto its image (certified, `57384ae`; naturality
`rfl`).  Consumes THE RESULT — closes on contact, no proof of its own. -/
instance ASection.residueTotal_isConnected (A : ASection) :
    CategoryTheory.IsConnected A.residueTotalCategory :=
  A.residueTotal_isConnected_of_transitive A.sweepTransitive_on_residueSystem

/-- **THE DECLARATION**: `π₀(∫𝓡_A)` IS A SINGLETON — CHT Remark 8.3.5 on
the connected action groupoid: nonempty and connected, so one class.
Instantiates the certified receipt
`residueTotal_pi0_singleton_of_connected`. -/
theorem ASection.residueTotal_pi0_singleton (A : ASection) :
    ∀ P Q : A.residueTotalCategory,
      CategoryTheory.ConnectedComponents.mk P =
        CategoryTheory.ConnectedComponents.mk Q := by
  letI := A.residueTotal_isConnected
  exact A.residueTotal_pi0_singleton_of_connected

/-- The A-specific instance of the Grothendieck component-colimit
equivalence, on the semantic C-residue input-groupoid diagram itself. -/
noncomputable def ASection.residueTotalPi0ColimitEquiv (A : ASection) :
    CategoryTheory.ConnectedComponents A.residueTotalCategory ≃
      Limits.colimit
        ((A.AsectionCResidueInputDiagram ⋙ Grpd.forgetToCat) ⋙ pi0Functor) :=
  pi0GrothendieckEquiv A.AsectionCResidueInputDiagram

/-- The component colimit of the connected semantic C-residue total is a
singleton. -/
theorem ASection.residueTotal_pi0_colimit_singleton (A : ASection) :
    ∀ κ₁ κ₂ : Limits.colimit
      ((A.AsectionCResidueInputDiagram ⋙ Grpd.forgetToCat) ⋙ pi0Functor),
      κ₁ = κ₂ := by
  intro κ₁ κ₂
  let e := A.residueTotalPi0ColimitEquiv
  rw [← e.apply_symm_apply κ₁, ← e.apply_symm_apply κ₂]
  apply congrArg e
  exact _root_.Quotient.inductionOn₂ (e.symm κ₁) (e.symm κ₂)
    (fun P Q => A.residueTotal_pi0_singleton P Q)

/-! ## The readout boundary (synchronized 2026-09-02)

The singleton collapse above is a statement about connected components of
`∫𝓡_A`.  It does not, by itself, compare the ordinary real reads
`A.transportLevel n` carried by two certified representatives: two objects of
one component are joined by a zigzag of transports, and no cocone, descent
law, or invariance law for `residueInputTotalTransportRead` along those
transports is proved.

The admitted pairwise equality that formerly closed this gap
(`ASection.residueTotal_transportLevel_singleton`, one `sorry`) and the
universal theorem it fed (`ASection.concentricity`, master
`thm:concentricity` in its former form) were withdrawn on 2026-09-02.  The
universal statement is false at this exact `ASection` type:
`SpecCandidate.current_ASection_concentricity_type_false`
(Concentricity/SpecCandidate.lean) exhibits a literal, field-complete
A-section whose enumerated zero-spheres do not share a centre.  What remains
here is the exact clean interface between the two formulations of the open
question; the zeta-specific answer is in Concentricity/Corollaries.lean. -/

/-- Common real centre for the enumerated residue-ℂ zero-spheres of an
A-section.  This is the conclusion the withdrawn universal theorem asserted
for every `A`; it is now a predicate, true for some A-sections and false for
others (`SpecCandidate.candidateSection_not_concentricASection`). -/
def ConcentricASection (A : ASection) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, (A.sphereZero n).re = c

/-- Equality of the real reads carried by all certified transport
representatives. -/
def PairwiseTransportLevel (A : ASection) : Prop :=
  ∀ n m : ℕ, A.transportLevel n = A.transportLevel m

/-- The two formulations are the same proposition, because the certified read
computes to the spherical-zero real part
(`ASection.transportLevel_eq_sphereZero_re`).  Consequently pairwise read
equality is not a weaker categorical surrogate for concentricity, and the
singleton collapse cannot supply it for a general A-section. -/
theorem concentricASection_iff_pairwiseTransportLevel (A : ASection) :
    ConcentricASection A ↔ PairwiseTransportLevel A := by
  constructor
  · rintro ⟨c, hc⟩ n m
    rw [A.transportLevel_eq_sphereZero_re,
      A.transportLevel_eq_sphereZero_re]
    exact (hc n).trans (hc m).symm
  · intro h
    refine ⟨(A.sphereZero 0).re, fun n => ?_⟩
    rw [← A.transportLevel_eq_sphereZero_re n,
      ← A.transportLevel_eq_sphereZero_re 0]
    exact h n 0
