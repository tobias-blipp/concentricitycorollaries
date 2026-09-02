> **STALE — pre-synchronization artifact (generated before 2026-09-02).**
> On 2026-09-02 the production surface was synchronized to the zeta-specific
> replacement: `ASection.concentricity`, `ASection.nontrivial_one_centre`, and
> `zeta_riemannHypothesis` were withdrawn (the universal statement is false;
> see `Concentricity/SpecCandidate.lean`), the repository now has zero
> `sorry`, and the headline surface is `Concentricity/Corollaries.lean`
> (`zetaSection_concentric_iff_RH` and companions). Rows below that mention the
> withdrawn names describe the old tree. Regenerate this file from the current
> sources before citing it. See `AGENTS.md`, section "STATUS 2026-09-02".

# Blueprint–Lean certificate table

Generated mechanically from the current master, current Lean sources, and the pinned toolchain.
The manifest is the single human-ratified mapping from a master clause to a Lean declaration; the generator verifies the exact master anchor, exact Lean type, fresh kernel run, axiom surface, and source fingerprints.
Regenerate with `scripts/generate_blueprint_lean_table.py`. The generator reads and probes `Concentricity/Theorem.lean`; it does not edit either production seat.

Current count: 15 terminal certificates; 9 inference certificates; 0 unpacked dossier bindings ready; 1 author bindings confirmed; 0 confirmed bindings awaiting Lean spelling; 0 production seats open.

Certificate meanings:

- `TERMINAL_CERTIFIED`: master `\lean{...}` link + fresh provider build/type check + exact allowed axiom surface.
- `INFERENCE_CERTIFIED`: exact master-clause anchor + focused current-source kernel proof + exact allowed axiom surface; production wiring may still be open.
- `OPEN_SEAT`: Lean reached the precise declaration/instantiation/wiring boundary printed below.

Allowed axiom surface: `['propext', 'Classical.choice', 'Quot.sound']`.

## Already terminal-certified

| Master semantics | Lean declaration | Master | Kernel/type | Axioms | Status |
|---|---|---:|---:|---:|---|
| G₂ supplies the remaining sphere-direction action | `G2.exists_smul_eq_of_mem_unitImaginarySphere` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| octonionic action world | `H1` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| slice-value world | `SphereWorld` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| projective action-groupoid base | `GreatCircle.Base` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| chosen orbit representative has the required endpoint | `GreatCircle.orbitRep_spec` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| total Grothendieck construction | `CategoryTheory.Grothendieck` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| C-residue zero locus | `ASection.CResidueZeroLocus` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| C-residue inverse-image diagram | `ASection.AsectionCResidueDiagram` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| inclusion of the inverse-image diagram in the total action diagram | `ASection.AsectionCResidueInclusion` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| semantic C-residue inverse-image input locus | `ASection.IsCResidueInput` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| semantic C-residue input groupoid | `ASection.CResidueInputWorld` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| the one distinguished disk action transports a locus arrow | `ASection.CResidueInputActionSquare` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| semantic input-locus action diagram | `ASection.AsectionCResidueInputDiagram` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| transitivity of the semantic C-residue Grothendieck total | `ASection.CResidueInputTotal_transitive` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |
| certified representative reads its carried real transport level | `ASection.residueInputTotalTransportRead_certified` | ✓ | ✓ | ✓ | `TERMINAL_CERTIFIED` |

## Triple-certified at the level of inference

| Master clause | Focused Lean receipt | Edge | Master/identity | Kernel/type | Axioms | Status |
|---|---|---|---:|---:|---:|---|
| the semantic inverse-image locus supplies a base arrow between arbitrary inputs | `ASection.CResidueInputHom_audit` (Concentricity/_GateNorthCResidueTransitivityAudit.lean:359) | `inference` | ✓ | ✓ | ✓ | `INFERENCE_CERTIFIED` |
| after base transport G₂ supplies the fibre component | `ASection.CResidueInputFiberHom_audit` (Concentricity/_GateNorthCResidueTransitivityAudit.lean:363) | `inference` | ✓ | ✓ | ✓ | `INFERENCE_CERTIFIED` |
| the base and fibre components form one Grothendieck morphism between arbitrary objects | `ASection.CResidueInputTotal_transitive_audit` (Concentricity/_GateNorthCResidueTransitivityAudit.lean:370) | `inference` | ✓ | ✓ | ✓ | `INFERENCE_CERTIFIED` |
| the production transitivity theorem consumes the semantic total directly | `ASection.sweepTransitive_on_residueSystem_audit` (Concentricity/_GateNorthCResidueTransitivityAudit.lean:374) | `inference` | ✓ | ✓ | ✓ | `INFERENCE_CERTIFIED` |
| transitivity of the exact ∫R_A implies IsConnected for that exact ∫R_A | `ASection.residueTotal_isConnected_of_transitive_audit` (Concentricity/_GateNorthCResidueTransitivityAudit.lean:385) | `inference` | ✓ | ✓ | ✓ | `INFERENCE_CERTIFIED` |
| connectedness of the exact ∫R_A makes π₀ of that exact ∫R_A a singleton | `ASection.residueTotal_pi0_singleton_of_connected_audit` (Concentricity/_GateNorthCResidueTransitivityAudit.lean:394) | `inference` | ✓ | ✓ | ✓ | `INFERENCE_CERTIFIED` |
| the general one-centre corollary is exactly the concentricity conclusion | `ASection.nontrivial_one_centre_of_concentricity_audit` (Concentricity/_GateCorollaryInferenceAudit.lean:13) | `identity` | ✓ | ✓ | ✓ | `INFERENCE_CERTIFIED` |
| the zeta specialization and proved concentricity equivalence imply RH | `zeta_riemannHypothesis_of_concentricity_audit` (Concentricity/_GateCorollaryInferenceAudit.lean:19) | `inference` | ✓ | ✓ | ✓ | `INFERENCE_CERTIFIED` |
| RH and the proved infinitude imply infinitely many critical-line zeros | `zeta_criticalLine_zeros_infinite_of_RH_audit` (Concentricity/_GateCorollaryInferenceAudit.lean:31) | `inference` | ✓ | ✓ | ✓ | `INFERENCE_CERTIFIED` |

## Binding identity layer

The first table records the project-specific objects already unpacked from the two arbitrary objects. The second table separates the author's confirmed mathematical binding from the typist's Lean spelling. Author confirmation hashes the master label, paper object, local role, and expected type; Lean then checks the recovered candidate expression independently at that exact type.

| Exact project-specific locals | Provenance | Source exact | Kernel reached consumer | Status |
|---|---|---:|---:|---|
| `xN, hxN, g, hg` | the inverse-image dossier carried by the arbitrary object P; `obtain ⟨xN, hxN, g, hg⟩ := P.fiber.property` | ✗ | ✗ | `BINDING_UNRESOLVED` |
| `yN, hyN, h, hh` | the inverse-image dossier carried by the arbitrary object Q; `obtain ⟨yN, hyN, h, hh⟩ := Q.fiber.property` | ✗ | ✗ | `BINDING_UNRESOLVED` |

| Paper object | Lean local | Expected type | Author binding | Master link and target | Candidate expression | Lean elaboration | Status |
|---|---|---|---|---:|---|---:|---|
| the post-collapse residue read instantiated at the n-th and 0-th certified representatives | `hkn` | `A.transportLevel n = A.transportLevel 0` | ✓ confirmed | ✗ | `A.residueTotal_transportLevel_singleton n 0` | — | `AUTHOR_BINDING_TARGET_MISMATCH` |

### Exact seat attempts

Lean was contacted with the exact candidate expression for: `seat2.transportLevelCollapse`. Each remaining row stays mandatory transcription work.

## Current production boundary

| Master result | Exact remaining role | Production declaration | Lean contact | Status |
|---|---|---|---:|---|
| `thm:concentricity` | the val step: the π₀-class equality instantiated at the n-th and 0-th certified representatives, carried across to the real-valued level equality | `ASection.residueTotal_transportLevel_singleton` (Concentricity/Theorem.lean:990) | — | `UNLOCATED_OPEN_SEAT` |

The current production run reaches exactly two errors: the north existential in `sweepTransitive_on_residueSystem` and the real-valued equality in `concentricity`. The inference table above is independently green against the exact current source prefix; the open seats do not downgrade those receipts.

## Exact checked types

### `G2.exists_smul_eq_of_mem_unitImaginarySphere`

```lean
G2.exists_smul_eq_of_mem_unitImaginarySphere : ∀ {u v : Octonion},
  u ∈ Octonion.unitImaginarySphere → v ∈ Octonion.unitImaginarySphere → ∃ g, g • u = v
```

### `H1`

```lean
H1 : Type
```

### `SphereWorld`

```lean
SphereWorld : Type
```

### `GreatCircle.Base`

```lean
GreatCircle.Base : Type
```

### `GreatCircle.orbitRep_spec`

```lean
GreatCircle.orbitRep_spec : ∀ (b : GreatCircle.Point), GreatCircle.orbitRep b • OnePoint.infty = b
```

### `CategoryTheory.Grothendieck`

```lean
CategoryTheory.Grothendieck : {C : Type u_1} →
  [inst : CategoryTheory.Category.{u_2, u_1} C] → CategoryTheory.Functor C CategoryTheory.Cat → Type (max u_1 u_3)
```

### `ASection.CResidueZeroLocus`

```lean
ASection.CResidueZeroLocus : ASection → Set ℂ
```

### `ASection.AsectionCResidueDiagram`

```lean
ASection.AsectionCResidueDiagram : ASection → CategoryTheory.Functor GreatCircle.Base CategoryTheory.Grpd
```

### `ASection.AsectionCResidueInclusion`

```lean
ASection.AsectionCResidueInclusion : (A : ASection) → A.AsectionCResidueDiagram ⟶ A.AsectionActionDiagram
```

### `ASection.IsCResidueInput`

```lean
ASection.IsCResidueInput : ASection →
  CategoryTheory.ObjectProperty (CategoryTheory.ActionCategory (↥Moebius) (OnePoint ℂ))
```

### `ASection.CResidueInputWorld`

```lean
ASection.CResidueInputWorld : ASection → Type
```

### `ASection.CResidueInputActionSquare`

```lean
ASection.CResidueInputActionSquare : (A : ASection) →
  {u v : A.CResidueInputWorld} →
    (u ⟶ v) →
      ASection.ActionTransportSquare (A.projectiveObjectFrame ASection.projectiveNorth)
        (A.projectiveObjectFrame ASection.projectiveNorth)
```

### `ASection.AsectionCResidueInputDiagram`

```lean
ASection.AsectionCResidueInputDiagram : (A : ASection) → CategoryTheory.Functor A.CResidueInputWorld CategoryTheory.Grpd
```

### `ASection.CResidueInputTotal_transitive`

```lean
ASection.CResidueInputTotal_transitive : ∀ (A : ASection) (P Q : A.CResidueInputTotalCategory), Nonempty (P ⟶ Q)
```

### `ASection.residueInputTotalTransportRead_certified`

```lean
ASection.residueInputTotalTransportRead_certified : ∀ (A : ASection) (n : ℕ) (I : SphereWorld),
  A.residueInputTotalTransportRead (A.residueInputTotalObject n I) = A.transportLevel n
```

### `ASection.CResidueInputHom_audit`

```lean
ASection.CResidueInputHom_audit : ∀ (A : ASection) (u v : A.CResidueInputWorld), Nonempty (u ⟶ v)
```

### `ASection.CResidueInputFiberHom_audit`

```lean
ASection.CResidueInputFiberHom_audit : ∀ (A : ASection) {u v : A.CResidueInputWorld} (f : u ⟶ v)
  (x : (A.IsCResidueStateOverInput u).FullSubcategory) (y : (A.IsCResidueStateOverInput v).FullSubcategory),
  Nonempty ((A.AsectionCResidueInputTransport f).obj x ⟶ y)
```

### `ASection.CResidueInputTotal_transitive_audit`

```lean
ASection.CResidueInputTotal_transitive_audit : ∀ (A : ASection) (P Q : A.CResidueInputTotalCategory), Nonempty (P ⟶ Q)
```

### `ASection.sweepTransitive_on_residueSystem_audit`

```lean
ASection.sweepTransitive_on_residueSystem_audit : ∀ (A : ASection) (P Q : A.residueTotalCategory), Nonempty (P ⟶ Q)
```

### `ASection.residueTotal_isConnected_of_transitive_audit`

```lean
ASection.residueTotal_isConnected_of_transitive_audit : ∀ (A : ASection),
  (∀ (P Q : A.residueTotalCategory), Nonempty (P ⟶ Q)) → CategoryTheory.IsConnected A.residueTotalCategory
```

### `ASection.residueTotal_pi0_singleton_of_connected_audit`

```lean
ASection.residueTotal_pi0_singleton_of_connected_audit : ∀ (A : ASection) [CategoryTheory.IsConnected A.residueTotalCategory]
  (P Q : A.residueTotalCategory), CategoryTheory.ConnectedComponents.mk P = CategoryTheory.ConnectedComponents.mk Q
```

### `ASection.nontrivial_one_centre_of_concentricity_audit`

```lean
ASection.nontrivial_one_centre_of_concentricity_audit : ∀ (A : ASection),
  (∃ c, ∀ (n : ℕ), (A.sphereZero n).re = c) → ∃ c, ∀ (n : ℕ), (A.sphereZero n).re = c
```

### `zeta_riemannHypothesis_of_concentricity_audit`

```lean
zeta_riemannHypothesis_of_concentricity_audit : (∃ c, ∀ (n : ℕ), (zetaSection.sphereZero n).re = c) → RiemannHypothesis
```

### `zeta_criticalLine_zeros_infinite_of_RH_audit`

```lean
zeta_criticalLine_zeros_infinite_of_RH_audit : RiemannHypothesis → {s | riemannZeta s = 0 ∧ s.re = 1 / 2}.Infinite
```

## Source fingerprints

| Source | SHA-256 |
|---|---|
| `Octonionic_RH_master.tex` | `5b533b14bed378b93acacc0e732a8c800c84bae38605d19beffdabd5bc39fb8a` |
| `blueprint/lean_certificate_manifest.json` | `5d1a8ec9cf2c3590d8c4d7e5aa87b278bb3f6906b13df44e5702f2a25b15a58f` |
| `Concentricity/_BlueprintTerminalCertificateProbe.lean` | `aeabd54553ba32bacb31183e3a2eff9f8cba0ca3973f2b518f127cfb249c4f18` |
| `Concentricity/Theorem.lean` | `2c11a6501285c9ab7cb5dcd4af89eca72b36e95cd047e7a9e1e254e397821d14` |
| `Concentricity/_GateNorthCResidueTransitivityAudit.lean` | `efd2bd6d7f5f6437b7d32bae8cbb51299c3724e148386a3b701add58edebeb8a` |
| `scripts/build_transitivity_inference_probe.sh` | `e0982829e4937b00e01bda1b7b4a4e767c09f3a907ae65393a4590125a686683` |
| `Concentricity/_GateCorollaryInferenceAudit.lean` | `8bac693ca5c93deae6b9f1511e3f058efab47a8b657c061fc178176fe5636efb` |
| `Concentricity/Corollaries.lean` | `4866f494cf62579778905d6dd93b912a868a880b827c4456a060bdb08d441248` |
| `lean-toolchain` | `efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee` |
| `lakefile.toml` | `361be5c558f10fbc113a616222d2db2c08c9b353ddb12f0cac6d5ad9a0d0287d` |
| `lean_source_tree` | `846186e593b0e44e121217b21ce185cdc1b6b4a970f4043a0a2011eebe81c4b7` |

Raw kernel output: `blueprint/lean_certificate_probe.txt`.
Machine-readable evidence: `blueprint/lean_certificate_evidence.json`.
Composition-free verdict: `blueprint/lean_inference_verdict.txt`.
Semantic manifest: `blueprint/lean_certificate_manifest.json`.
