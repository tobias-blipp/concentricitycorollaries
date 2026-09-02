> **STALE — pre-synchronization artifact (generated before 2026-09-02).**
> On 2026-09-02 the production surface was synchronized to the zeta-specific
> replacement: `ASection.concentricity`, `ASection.nontrivial_one_centre`, and
> `zeta_riemannHypothesis` were withdrawn (the universal statement is false;
> see `Concentricity/SpecCandidate.lean`), the repository now has zero
> `sorry`, and the headline surface is `Concentricity/Corollaries.lean`
> (`zetaSection_concentric_iff_RH` and companions). Rows below that mention the
> withdrawn names describe the old tree. Regenerate this file from the current
> sources before citing it. See `AGENTS.md`, section "STATUS 2026-09-02".

# RelevantGreenFinal

What is certified. Elicited from the kernel on 2026-07-28, not recalled. Every declaration below
prints exactly

```text
[propext, Classical.choice, Quot.sound]
```

— Mathlib's three foundations. **Zero project axioms anywhere on this list.**

Regenerate by `#print axioms` on these names; do not hand-edit.

---

## The distinguished element and its positioning

| declaration | note |
|---|---|
| `ASection.distinguishedDiskAction` | the element, in `Moebius` |
| `ASection.distinguishedDiskAction_fixes_cayley_zero` | Euler's face at `0` |
| `ASection.distinguishedDiskAction_fixes_cayley_N` | Weierstrass's face at `N` |
| `ASection.projectiveObjectFrame` | the element positioned at a frame |
| `ASection.projectiveObjectFrame_north` | **at north the frame IS the element** |
| `ASection.projectiveArrowElement` | its conjugation along a base arrow |
| `GreatCircle.orbit_stabilizer_factor` | existence of the factorization |
| `GreatCircle.stabilizerPart_unique` | its uniqueness |

## The functor, its laws, its squares, its total

`ASection.AsectionActionFiber` · `ASection.AsectionActionTransport` ·
`ASection.AsectionActionTransport_id` · `ASection.AsectionActionTransport_comp` ·
`ASection.AsectionActionDiagram` (= `F_A`) · `ASection.TotalActionStateWorld` (= `T_A`) ·
`ASection.orbitStabilizerActionSquare` · `ASection.positionedOrbitSquare` ·
`ASection.AsectionEquivariant` (`H1 ⥤ H1`, the sweep — `ASectionEquivariant.lean:43`; elicited
2026-07-28 night, exactly the three foundations)

## C3 / C4 and the semantic locus

`ASection.CResidueZeroLocus` · `ASection.sphereZero_mem_CResidueZeroLocus` ·
`ASection.CResidueZeroLocus_infinite` (C4) · `ASection.sphereZero_complete`

## The preimage and `ι_A`

`ASection.IsNorthCResidueState` · `ASection.IsCResidueState` ·
`ASection.AsectionCResidueTransport` (= `𝓡_A(f)`) · `ASection.AsectionCResidueDiagram` (= `𝓡_A`) ·
`ASection.AsectionCResidueInclusion` (**naturality by `rfl`**, `57384ae`) and
`…_app_fullyFaithful` / `…_app_full` / `…_app_faithful` (`Theorem.lean:372`, `:377`, `:382`,
`bb02b54`) — these are the **componentwise presentation**.

**`ι_A` AT THE TOTAL — the inclusion of the inverse image IN the total, which is what `ι_A` is:**
`ASection.AsectionCResidueInclusionTotal` (`Grothendieck.map` of the whiskered inclusion,
`∫𝓡_A ⥤ T_A`) · `…Total_faithful` · `…Total_full` — **`b073d88`**, all three on exactly the three
foundations. Together they make it an **isomorphism onto its image inside the total**. Mathlib has
no lemma that `Grothendieck.map` preserves fullness or faithfulness (`Grothendieck.lean` carries
`map` `:242`, `map_map` `:262`, `faithful_ι` `:560` for the *fibre* inclusion, nothing else) —
these put it under a name.

## Inhabitants

`ASection.residueActionState` · `ASection.residueActionState_positioned` ·
`ASection.residueTotal` — *cite at `ASectionTotalActionState.lean:117`; the name is shadowed in
the now-removed per-zero north-leg preflight.*

## The π₀ engine and the level

`pi0Functor` · `toColimitObj_eq_of_zigzag` · `pi0GrothendieckEquiv` · `pi0_grothendieck` ·
`ASection.transportLevel` (`= (A.sphereZero n).re`, by definition)

## Elsewhere in the tree, and NOT suppliers for the transcription seats

`G2.exists_smul_eq_of_mem_unitImaginarySphere` (green) · `sphereWorld_zigzag`
(`SliceSphereWorld.lean:288`) — a `𝒮₂`/slice-world fact, consumed by no certificate
(`Corollaries.lean` cites `ASection.concentricity`, nothing else) ·
`ASection.AsectionEquivariant_transitive` (`6596e04`) · `…_transitive_states` (`8907f88`) — green,
quantify over the ambient world, name `ι_A` nowhere. **None of these is at the register of the live
term** (see `EndgameFinal.md` §0 and §3).

## Downstream, already proved

`riemannHypothesis_iff_concentric` — **its right-hand side contains no `1/2`**; it asserts only a
common centre. `upperZero_re_eq_half_of_concentric` — `1/2` derived from the functional equation,
and it enters in that one file only.

## Build state

```text
lake build Concentricity.Corollaries   →  Build completed successfully (3694 jobs)
lake build (root)                      →  3693/3695; the endpoint awaited the two transcription
                                          seats in Theorem.lean
```

`Corollaries.lean` compiles against `A.concentricity`: `ASection.nontrivial_one_centre`,
`zeta_riemannHypothesis`, `zeta_criticalLine_zeros_infinite` all typecheck against the statement
as written. The corollary layer is wired and waiting.

## From Mathlib, at the pin — the argument's own machinery

`ActionCategory` (a category of elements, `Action.lean:48`) · `hom_as_subtype` (`:92`) ·
`instance … : IsConnected (ActionCategory M X)` (`:128`) · `instance : Groupoid` (`:137`) ·
`stabilizerIsoEnd` (`:105`, `MulEquiv.refl`) · `homOfPair` (`:146`) · `ActionCategory.cases`
(`:154`) · `ConnectedComponents := Quotient (Zigzag.setoid)` · `zigzag_isConnected` ·
`isPreconnected_zigzag` · `Grothendieck.map` · `Grothendieck.functor_comp_forget` ·
`ObjectProperty.lift` / `ι` / `fullyFaithfulι` / `liftCompιIso`

## Remaining Lean transcription

Two sites, both in `Theorem.lean`, coordinates re-elicited 2026-07-29:

```text
:445   ASection.sweepTransitive_on_residueSystem   -- ι_A is a transitive action groupoid
:528   the level clause inside ASection.concentricity
```

They are formalization seats, not outstanding mathematical inferences. **Nothing else in the
repository is open.**

The statement at `:445` is the author's lemma, at the total and naming no group: *any two
projective squares in the C-residue image — the objects of `∫𝓡_A` — are connected by one groupoid
element.* See `EndgameFinal.md`.
