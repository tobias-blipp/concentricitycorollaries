/-
Concentricity/ZetaCstar.lean

Islands A1–A2 (PLAN_islands_part1_part2_2026-07-05.md): the compactified
classical zeta ζ_ℂ* on ℂ* = OnePoint ℂ (master `def:zeta-Cstar`) and the
zero-preservation lemma (master `lem:zero-Cstar`). Part-1 objects only:
nothing octonionic, nothing about the class, no consumption of Island P.

`sorry` marks UNFORMALIZED, never UNSOUND (R8). This file targets ZERO
sorries.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Compactification.OnePoint.Basic

noncomputable section

open scoped OnePoint

/-- **The compactified classical zeta** (master `def:zeta-Cstar`, as corrected
2026-09-02): "ζ_ℂ* : ℂ* → ℂ* is the meromorphic continuation of ζ regarded as
a map to the Riemann sphere: ζ_ℂ*(s) = ζ(s) for s ∈ ℂ∖{1}; ζ_ℂ*(1) = ∞ (the
simple pole, Theorem thm:riemann); and ζ_ℂ*(∞) = 1, a conventional value at
the adjoined domain point.  On the finite plane ζ_ℂ* is holomorphic into ℂ*
on ℂ∖{1}, its sole pole being s = 1.  It is not continuous at the domain point
∞, and no continuous extension exists there."  (The earlier quoted clause
"holomorphic into ℂ* on ℂ*∖{1}" was false and was withdrawn.)

Rendered on Mathlib's `OnePoint ℂ` (the master's own Lean pointer for the
one-point compactification, `rmk:G2-compact`), over Mathlib's `riemannZeta`
(the continuation of `thm:riemann`; R5 pin verified live v4.31.0). -/
def zetaC : OnePoint ℂ → OnePoint ℂ
  | ∞ => ((1 : ℂ) : OnePoint ℂ)
  | (s : ℂ) => if s = 1 then ∞ else ((riemannZeta s : ℂ) : OnePoint ℂ)

/-- `def:zeta-Cstar`, clause "ζ_ℂ*(s) = ζ(s) for s ∈ ℂ∖{1}". -/
theorem zetaC_coe {s : ℂ} (hs : s ≠ 1) :
    zetaC (s : OnePoint ℂ) = ((riemannZeta s : ℂ) : OnePoint ℂ) := by
  simp [zetaC, hs]

/-- `def:zeta-Cstar`, clause "ζ_ℂ*(1) = ∞ (the simple pole)". -/
theorem zetaC_one : zetaC ((1 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [zetaC]

/-- `def:zeta-Cstar`, clause "ζ_ℂ*(∞) = 1". -/
theorem zetaC_infty : zetaC ∞ = ((1 : ℂ) : OnePoint ℂ) := rfl

/-- **Zero preservation at a finite point** (master `lem:zero-Cstar`,
forward half at the coordinate): a finite point is a zero of ζ_ℂ* iff it is
a zero of ζ away from the pole. Stated with the `s ≠ 1` clause so the
statement is junk-value-robust: at `s = 1` the left side is the pole value
∞ ≠ 0 and the right side is false by the clause — no appeal to any
convention for `riemannZeta 1`. -/
theorem zetaC_coe_eq_zero_iff {s : ℂ} :
    zetaC (s : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
      ↔ riemannZeta s = 0 ∧ s ≠ 1 := by
  by_cases hs : s = 1
  · subst hs
    simp [zetaC_one]
  · rw [zetaC_coe hs, OnePoint.coe_eq_coe]
    exact ⟨fun h => ⟨h, hs⟩, fun h => h.1⟩

/-- **The compactification does not move the zeros** (master
`lem:zero-Cstar`, verbatim): "Z(ζ_ℂ*) = Z(ζ): the zeros of ζ_ℂ* in ℂ* are
exactly the zeros of ζ in ℂ; in particular the nontrivial zeros coincide."
Master proof clauses carried: "The two adjoined values are not zeros:
ζ_ℂ*(1) = ∞ (a pole) and ζ_ℂ*(∞) = 1; and s = 1, being a pole of ζ, was
never a zero. Hence no zero is gained or lost." -/
theorem zetaC_zero_iff (x : OnePoint ℂ) :
    zetaC x = ((0 : ℂ) : OnePoint ℂ)
      ↔ ∃ s : ℂ, x = (s : OnePoint ℂ) ∧ riemannZeta s = 0 ∧ s ≠ 1 := by
  cases x with
  | infty =>
    -- x = ∞: ζ_ℂ*(∞) = 1 ≠ 0, and ∞ is no coordinate point
    constructor
    · intro h
      rw [zetaC_infty, OnePoint.coe_eq_coe] at h
      exact absurd h one_ne_zero
    · rintro ⟨s, hs, -⟩
      exact absurd hs (OnePoint.infty_ne_coe s)
  | coe s =>
    rw [zetaC_coe_eq_zero_iff]
    constructor
    · intro h
      exact ⟨s, rfl, h⟩
    · rintro ⟨t, ht, h⟩
      rw [OnePoint.coe_eq_coe] at ht
      subst ht
      exact h
