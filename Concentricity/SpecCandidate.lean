/-
Concentricity/SpecCandidate.lean

A literal, field-complete `ASection` whose enumerated residue-ℂ zero-spheres
do not share a centre.  Its stem is `(z^2 + 1) * riemannZeta z`: the checked
zeta section multiplied by the conjugate-paired genus-zero primary factor of
the extra upper-half-plane zero `i`.  Every structure field is discharged
below — the individually zero-free infinite Euler-log family, both
local-normal majorants, the simple pole at `1`, the full factorization, the
lower-edge and at-`N` clauses, and the infinite zero range.

Its enumerated zeros are `i` followed by the checked `zetaSphereZero`
enumeration.  The prepended zero has real part `0`; every inherited zeta zero
has real part strictly between `0` and `1` by the repository's strip theorem
(`nontrivialZero_re_mem_Ioo`).  Hence the section is nonconcentric, and the
former universal proposition "every A-section is concentric" is false at this
exact `ASection` type (`current_ASection_concentricity_type_false`).

Provenance: elaborated on 2026-08-08 against the unchanged proof snapshot
(Concentricity-Analysis, TASK-0001, axiom surface
`[propext, Classical.choice, Quot.sound]`); installed in production on
2026-09-02.  This file adds ZERO sorries.
-/
import Concentricity.ZetaSection
import Concentricity.Theorem

noncomputable section

open Complex

namespace SpecCandidate

/-- One new upper-half-plane zero, deliberately left of the open zeta strip. -/
def extraZero : ℂ := Complex.I

/-- The conjugate-paired genus-zero primary factor for `extraZero`. -/
def extraPrimary (z : ℂ) : ℂ := spherePrimary 0 extraZero z

theorem extraPrimary_eq (z : ℂ) :
    extraPrimary z = z ^ 2 + 1 := by
  rw [extraPrimary, spherePrimary, weierstrassE, weierstrassE]
  simp [extraZero]
  rw [div_neg, Complex.div_I]
  simp only [neg_neg]
  calc
    (1 + z * Complex.I) * (1 - z * Complex.I)
        = 1 - (z * Complex.I) ^ 2 := by ring
    _ = 1 - z ^ 2 * Complex.I ^ 2 := by rw [mul_pow]
    _ = z ^ 2 + 1 := by rw [Complex.I_sq]; ring

theorem extraPrimary_re (z : ℂ) :
    (extraPrimary z).re = z.re ^ 2 - z.im ^ 2 + 1 := by
  rw [extraPrimary_eq]
  rw [pow_two]
  simp [Complex.mul_re]
  ring

theorem extraPrimary_im (z : ℂ) :
    (extraPrimary z).im = 2 * z.re * z.im := by
  rw [extraPrimary_eq]
  rw [pow_two]
  simp [Complex.mul_im]
  ring

/-- Global intrinsic symmetrization of the principal logarithm of the added
factor. On the Euler half-plane it reduces to the ordinary principal log. -/
def extraLog (z : ℂ) : ℂ :=
  (Complex.log (extraPrimary z) +
    starRingEnd ℂ (Complex.log (extraPrimary (starRingEnd ℂ z)))) / 2

theorem extraPrimary_intrinsic : IsIntrinsic extraPrimary := by
  intro z
  rw [extraPrimary_eq, extraPrimary_eq]
  simp only [map_add, map_pow, map_one]

theorem extraLog_intrinsic : IsIntrinsic extraLog := by
  intro z
  rw [extraLog, extraLog]
  simp only [map_div₀, map_add, map_ofNat, starRingEnd_self_apply]
  ring

theorem extraPrimary_ne_zero {z : ℂ} (hz : (1 : ℝ) < z.re) :
    extraPrimary z ≠ 0 := by
  intro h0
  have him : 2 * z.re * z.im = 0 := by
    rw [← extraPrimary_im z, h0]
    rfl
  have hxy : z.re * z.im = 0 := by linarith
  have hre : z.re ≠ 0 := ne_of_gt (by linarith)
  have hiz : z.im = 0 := (mul_eq_zero.mp hxy).resolve_left hre
  have hrez : (extraPrimary z).re = 0 := by rw [h0]; rfl
  rw [extraPrimary_re, hiz] at hrez
  norm_num at hrez
  nlinarith [sq_nonneg z.re]

theorem extraPrimary_ne_one {z : ℂ} (hz : (1 : ℝ) < z.re) :
    extraPrimary z ≠ 1 := by
  intro h1
  have him : 2 * z.re * z.im = 0 := by
    rw [← extraPrimary_im z, h1]
    rfl
  have hxy : z.re * z.im = 0 := by linarith
  have hre : z.re ≠ 0 := ne_of_gt (by linarith)
  have hiz : z.im = 0 := (mul_eq_zero.mp hxy).resolve_left hre
  have hrez : (extraPrimary z).re = 1 := by rw [h1]; rfl
  rw [extraPrimary_re, hiz] at hrez
  norm_num at hrez
  nlinarith [sq_nonneg z.re]

theorem extraPrimary_arg_ne_pi {z : ℂ} (hz : (1 : ℝ) < z.re) :
    (extraPrimary z).arg ≠ Real.pi := by
  intro harg
  obtain ⟨hre_neg, him⟩ := Complex.arg_eq_pi_iff.mp harg
  rw [extraPrimary_im] at him
  have hxy : z.re * z.im = 0 := by linarith
  have hre : z.re ≠ 0 := ne_of_gt (by linarith)
  have hiz : z.im = 0 := (mul_eq_zero.mp hxy).resolve_left hre
  rw [extraPrimary_re, hiz] at hre_neg
  norm_num at hre_neg
  nlinarith [sq_nonneg z.re]

theorem extraPrimary_mem_slitPlane {z : ℂ} (hz : (1 : ℝ) < z.re) :
    extraPrimary z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff_arg.mpr
    ⟨extraPrimary_arg_ne_pi hz, extraPrimary_ne_zero hz⟩

theorem extraLog_eq_log {z : ℂ} (hz : (1 : ℝ) < z.re) :
    extraLog z = Complex.log (extraPrimary z) := by
  rw [extraLog, extraPrimary_intrinsic z,
    Complex.log_conj _ (extraPrimary_arg_ne_pi hz)]
  simp

theorem extraLog_ne_zero {z : ℂ} (hz : (1 : ℝ) < z.re) :
    extraLog z ≠ 0 := by
  rw [extraLog_eq_log hz]
  intro hlog
  have hexp := congrArg Complex.exp hlog
  rw [Complex.exp_log (extraPrimary_ne_zero hz), Complex.exp_zero] at hexp
  exact extraPrimary_ne_one hz hexp

theorem extraLog_analyticAt : ∀ z : ℂ, (1 : ℝ) < z.re →
    AnalyticAt ℂ extraLog z := by
  intro z hz
  have hopen : IsOpen {w : ℂ | (1 : ℝ) < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hzmem : z ∈ {w : ℂ | (1 : ℝ) < w.re} := hz
  have hG : AnalyticAt ℂ (fun w => Complex.log (extraPrimary w)) z := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hopen z hzmem
    have hP : DifferentiableAt ℂ extraPrimary w := by
      have hfun : extraPrimary = fun u => u ^ 2 + 1 := funext extraPrimary_eq
      rw [hfun]
      fun_prop
    exact ((Complex.differentiableAt_log (extraPrimary_mem_slitPlane hw)).comp w hP).differentiableWithinAt
  refine hG.congr ?_
  filter_upwards [hopen.mem_nhds hzmem] with w hw
  exact (extraLog_eq_log hw).symm

def extraLogTerm (n : ℕ) (z : ℂ) : ℂ :=
  (extraLog z / 2) * ((1 / 2 : ℂ) ^ n)

theorem extraLogTerm_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => extraLogTerm n z) (extraLog z) := by
  have hgeom : HasSum (fun n : ℕ => ((1 / 2 : ℂ) ^ n)) 2 := by
    have h := hasSum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℂ)) (by norm_num)
    have htwo : (1 - (1 / 2 : ℂ))⁻¹ = 2 := by norm_num
    rw [htwo] at h
    exact h
  have hmul := hgeom.mul_left (extraLog z / 2)
  change HasSum (fun n : ℕ => (extraLog z / 2) * ((1 / 2 : ℂ) ^ n)) (extraLog z)
  have hval : extraLog z / 2 * 2 = extraLog z := by field_simp
  simpa only [hval] using hmul

theorem extraLogTerm_intrinsic (n : ℕ) : IsIntrinsic (extraLogTerm n) := by
  intro z
  rw [extraLogTerm, extraLogTerm, extraLog_intrinsic z]
  simp only [map_mul, map_div₀, map_ofNat, map_pow, map_one]

theorem extraLogTerm_analyticAt (n : ℕ) (z : ℂ) (hz : (1 : ℝ) < z.re) :
    AnalyticAt ℂ (extraLogTerm n) z := by
  change AnalyticAt ℂ (fun w => (extraLog w / 2) * ((1 / 2 : ℂ) ^ n)) z
  exact (extraLog_analyticAt z hz).div_const.mul analyticAt_const

theorem extraLogTerm_ne_zero (n : ℕ) (z : ℂ) (hz : (1 : ℝ) < z.re) :
    extraLogTerm n z ≠ 0 := by
  rw [extraLogTerm]
  exact mul_ne_zero (div_ne_zero (extraLog_ne_zero hz) (by norm_num)) (pow_ne_zero _ (by norm_num))

abbrev CandidateEulerIndex := Nat.Primes ⊕ ℕ

def candidateEulerLog : CandidateEulerIndex → ℂ → ℂ
  | Sum.inl p => zetaEulerLog p
  | Sum.inr n => extraLogTerm n

theorem candidateC2_intrinsic : ∀ p, IsIntrinsic (candidateEulerLog p) := by
  rintro (p | n)
  · exact zetaC2_intrinsic p
  · exact extraLogTerm_intrinsic n

theorem candidateC2_analyticAt : ∀ p, ∀ z : ℂ, (1 : ℝ) < z.re →
    AnalyticAt ℂ (candidateEulerLog p) z := by
  rintro (p | n) z hz
  · exact zetaC2_analyticAt p z hz
  · exact extraLogTerm_analyticAt n z hz

theorem candidateC2_zero_free : ∀ p, ∀ z : ℂ, (1 : ℝ) < z.re →
    candidateEulerLog p z ≠ 0 := by
  rintro (p | n) z hz
  · exact zetaC2_zero_free p z hz
  · exact extraLogTerm_ne_zero n z hz

theorem candidateC2_summable : ∀ z : ℂ, (1 : ℝ) < z.re →
    Summable fun p => candidateEulerLog p z := by
  intro z hz
  apply Summable.sum (fun p => candidateEulerLog p z)
  · simpa [candidateEulerLog, Function.comp_def] using zetaC2_summable z hz
  · simpa [candidateEulerLog, Function.comp_def] using (extraLogTerm_hasSum z).summable

theorem candidateC2_locMajorant : ∀ z : ℂ, (1 : ℝ) < z.re →
    ∃ r > 0, ∃ u : CandidateEulerIndex → ℝ, Summable u ∧
      ∀ p, ∀ w ∈ Metric.ball z r, ‖candidateEulerLog p w‖ ≤ u p := by
  intro z hz
  obtain ⟨rz, hrz, uz, huz, hzbound⟩ := zetaC2_locMajorant z hz
  obtain ⟨rl, hrl, hl⟩ :=
    Metric.continuousAt_iff.mp (extraLog_analyticAt z hz).continuousAt 1 (by norm_num)
  let M : ℝ := ‖extraLog z‖ + 1
  let vg : ℕ → ℝ := fun n => M * ((1 / 2 : ℝ) ^ n)
  let u : CandidateEulerIndex → ℝ
    | Sum.inl p => uz p
    | Sum.inr n => vg n
  refine ⟨min rz rl, lt_min hrz hrl, u, ?_, ?_⟩
  · apply Summable.sum u
    · simpa [u, Function.comp_def] using huz
    · have hg : Summable fun n : ℕ => ((1 / 2 : ℝ) ^ n) :=
        summable_geometric_of_norm_lt_one (by norm_num)
      simpa [u, vg, Function.comp_def] using hg.mul_left M
  · rintro (p | n) w hw
    · apply hzbound p w
      exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
    · have hwl : dist w z < rl :=
        lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_right _ _)
      have hout : dist (extraLog w) (extraLog z) < 1 := hl hwl
      have hnorm := norm_le_norm_add_norm_sub (extraLog z) (extraLog w)
      have hout' : ‖extraLog z - extraLog w‖ < 1 := by
        simpa [dist_eq_norm, norm_sub_rev] using hout
      have hL : ‖extraLog w‖ < M := by
        dsimp [M]
        linarith
      change ‖extraLogTerm n w‖ ≤ vg n
      rw [extraLogTerm, norm_mul, norm_div, norm_pow]
      norm_num
      dsimp [vg]
      have hp : 0 ≤ (1 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) n
      have hn : 0 ≤ ‖extraLog w‖ := norm_nonneg _
      nlinarith

theorem candidateEulerLog_tsum (z : ℂ) (hz : (1 : ℝ) < z.re) :
    (∑' p, candidateEulerLog p z) =
      (∑' p : Nat.Primes, zetaEulerLog p z) + extraLog z := by
  have h : HasSum (fun p => candidateEulerLog p z)
      ((∑' p : Nat.Primes, zetaEulerLog p z) + extraLog z) := by
    apply HasSum.sum
    · simpa [candidateEulerLog, Function.comp_def] using (zetaC2_summable z hz).hasSum
    · simpa [candidateEulerLog, Function.comp_def] using extraLogTerm_hasSum z
  exact h.tsum_eq

def candidateF (z : ℂ) : ℂ := extraPrimary z * riemannZeta z

theorem candidateC2_euler : ∀ z : ℂ, (1 : ℝ) < z.re →
    candidateF z = Complex.exp (∑' p, candidateEulerLog p z) := by
  intro z hz
  rw [candidateF, candidateEulerLog_tsum z hz, Complex.exp_add,
    ← zetaC2_euler z hz, extraLog_eq_log hz,
    Complex.exp_log (extraPrimary_ne_zero hz)]
  ring

theorem extraPrimary_analyticAt (z : ℂ) : AnalyticAt ℂ extraPrimary z := by
  have hfun : extraPrimary = fun w => w ^ 2 + 1 := funext extraPrimary_eq
  rw [hfun]
  fun_prop

theorem candidateF_intrinsic : IsIntrinsic candidateF := by
  intro z
  rw [candidateF, candidateF, extraPrimary_intrinsic z, riemannZeta_intrinsic z]
  exact (map_mul (starRingEnd ℂ) _ _).symm

theorem candidateF_meromorphic : MeromorphicOn candidateF Set.univ := by
  intro z _
  exact (extraPrimary_analyticAt z).meromorphicAt.mul
    (riemannZeta_meromorphicOn z (Set.mem_univ z))

theorem candidateF_analyticAt : ∀ z : ℂ, z ≠ (1 : ℂ) → AnalyticAt ℂ candidateF z := by
  intro z hz
  exact (extraPrimary_analyticAt z).mul (riemannZeta_analyticAt hz)

theorem extraPrimary_one : extraPrimary 1 = 2 := by
  rw [extraPrimary_eq]
  norm_num

theorem candidateF_simple :
    meromorphicOrderAt candidateF (1 : ℂ) = ((-1 : ℤ) : WithTop ℤ) := by
  have hfun : candidateF = extraPrimary * riemannZeta := rfl
  rw [hfun, meromorphicOrderAt_mul_of_ne_zero (extraPrimary_analyticAt 1)]
  · exact riemannZeta_orderAt_one
  · rw [extraPrimary_one]
    norm_num

/-- Prepend the new zero once, then retain the complete zeta enumeration. -/
def candidateSphereZero : ℕ → ℂ
  | 0 => extraZero
  | n + 1 => zetaSphereZero n

def candidateGenus : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

theorem candidateC3_multipliable : ∀ z : ℂ,
    Multipliable fun n => spherePrimary (candidateGenus n) (candidateSphereZero n) z := by
  intro z
  let f : ℕ → ℂ := fun n => spherePrimary (candidateGenus n) (candidateSphereZero n) z
  have htail : Multipliable fun n => f (n + 1) := by
    simpa [f, candidateGenus, candidateSphereZero, Nat.add_comm] using zetaC3_multipliable z
  exact ⟨_, htail.hasProd.prod_range_mul⟩

theorem candidate_tprod_eq (z : ℂ) :
    (∏' n, spherePrimary (candidateGenus n) (candidateSphereZero n) z) =
      extraPrimary z * (∏' n, spherePrimary n (zetaSphereZero n) z) := by
  let f : ℕ → ℂ := fun n => spherePrimary (candidateGenus n) (candidateSphereZero n) z
  have htail : Multipliable fun n => f (n + 1) := by
    simpa [f, candidateGenus, candidateSphereZero, Nat.add_comm] using zetaC3_multipliable z
  have h := tprod_eq_zero_mul' htail
  simpa [f, candidateGenus, candidateSphereZero, extraPrimary, Nat.add_comm] using h

theorem norm_extraPrimary_sub_one (w : ℂ) :
    ‖extraPrimary w - 1‖ = ‖w‖ ^ 2 := by
  rw [extraPrimary_eq]
  have h : w ^ 2 + 1 - 1 = w ^ 2 := by ring
  rw [h, norm_pow]

theorem candidateC3_locMajorant : ∀ z : ℂ, z ≠ (1 : ℂ) →
    ∃ r > 0, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, ∀ w ∈ Metric.ball z r,
        ‖spherePrimary (candidateGenus n) (candidateSphereZero n) w - 1‖ ≤ u n := by
  intro z hz
  obtain ⟨r, hr, u, hu, hbound⟩ := zetaC3_locMajorant z hz
  let C : ℝ := (‖z‖ + r) ^ 2
  let v : ℕ → ℝ
    | 0 => C
    | n + 1 => u n
  refine ⟨r, hr, v, ?_, ?_⟩
  · have htail : Summable fun n => v (n + 1) := by
      simpa [v, Nat.add_comm] using hu
    exact ⟨_, htail.hasSum.sum_range_add⟩
  · intro n w hw
    cases n with
    | zero =>
        rw [candidateGenus, candidateSphereZero]
        change ‖extraPrimary w - 1‖ ≤ C
        rw [norm_extraPrimary_sub_one]
        have hdist : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
        have hdist' : ‖z - w‖ < r := by simpa [norm_sub_rev] using hdist
        have hnorm := norm_le_norm_add_norm_sub z w
        have hn : ‖w‖ < ‖z‖ + r := by linarith
        dsimp [C]
        nlinarith [norm_nonneg w, norm_nonneg z]
    | succ n =>
        simpa [candidateGenus, candidateSphereZero, v] using hbound n w hw

theorem candidateC3_lowerEdge :
    ∃ βlo : ℝ, ∀ k : ℕ, βlo ≤ (candidateSphereZero k).re := by
  refine ⟨0, ?_⟩
  intro k
  cases k with
  | zero => simp [candidateSphereZero, extraZero]
  | succ n =>
      have hz := zetaSphereZero_zero n
      have him := zetaSphereZero_im_pos n
      obtain ⟨htriv, hone⟩ := nontrivial_of_im_ne_zero (ne_of_gt him)
      simpa [candidateSphereZero] using (nontrivialZero_re_mem_Ioo hz htriv hone).1.le

theorem candidateC3_atN :
    Summable fun n => 1 / (1 + ‖candidateSphereZero n‖ ^ 2) := by
  let f : ℕ → ℝ := fun n => 1 / (1 + ‖candidateSphereZero n‖ ^ 2)
  have htail : Summable fun n => f (n + 1) := by
    simpa [f, candidateSphereZero, Nat.add_comm] using zetaSphereZero_density
  exact ⟨_, htail.hasSum.sum_range_add⟩

theorem candidateC4_infinite : (Set.range candidateSphereZero).Infinite := by
  apply zetaSphereZero_range_infinite.mono
  rintro z ⟨n, rfl⟩
  exact ⟨n + 1, by simp [candidateSphereZero]⟩

theorem candidateC3_factorization : ∀ z : ℂ, z ≠ (1 : ℂ) →
    (z - (1 : ℂ)) * candidateF z =
      z ^ 0 * zetaRfac z * Complex.exp (zetaGfac z) *
        ∏' n, spherePrimary (candidateGenus n) (candidateSphereZero n) z := by
  intro z hz
  rw [candidateF, candidate_tprod_eq]
  have hzet := zetaC3_factorization z hz
  have hzet' : (z - (1 : ℂ)) * riemannZeta z =
      z ^ 0 * zetaRfac z * Complex.exp (zetaGfac z) *
        ∏' n, spherePrimary n (zetaSphereZero n) z := by
    simpa using hzet
  calc
    (z - 1) * (extraPrimary z * riemannZeta z)
        = extraPrimary z * ((z - 1) * riemannZeta z) := by ring
    _ = extraPrimary z *
        (z ^ 0 * zetaRfac z * Complex.exp (zetaGfac z) *
          ∏' n, spherePrimary n (zetaSphereZero n) z) := by rw [hzet']
    _ = z ^ 0 * zetaRfac z * Complex.exp (zetaGfac z) *
          (extraPrimary z * ∏' n, spherePrimary n (zetaSphereZero n) z) := by ring

theorem extraZero_im : extraZero.im = 1 := by
  simp [extraZero]

theorem extraZero_re : extraZero.re = 0 := by
  simp [extraZero]

theorem candidateSphereZero_im_pos : ∀ n, 0 < (candidateSphereZero n).im := by
  intro n
  cases n with
  | zero => simp [candidateSphereZero, extraZero]
  | succ n => simpa [candidateSphereZero] using zetaSphereZero_im_pos n

theorem zetaSphereZero_re_pos (n : ℕ) : 0 < (zetaSphereZero n).re := by
  have hz := zetaSphereZero_zero n
  have him := zetaSphereZero_im_pos n
  obtain ⟨htriv, hone⟩ := nontrivial_of_im_ne_zero (ne_of_gt him)
  exact (nontrivialZero_re_mem_Ioo hz htriv hone).1

theorem candidate_not_concentric :
    ¬ ∃ c : ℝ, ∀ n : ℕ, (candidateSphereZero n).re = c := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  have hp := zetaSphereZero_re_pos 0
  simp [candidateSphereZero, extraZero] at h0 h1
  linarith

/-- A literal field-complete `ASection` obtained by multiplying the checked
zeta section by the conjugate-paired polynomial `z^2 + 1`. -/
noncomputable def candidateSection : ASection where
  F := candidateF
  intrinsic := candidateF_intrinsic
  meromorphic := candidateF_meromorphic
  pole := 1
  c1_analyticAt := by
    intro z hz
    apply candidateF_analyticAt z
    simpa using hz
  c1_simple := by simpa using candidateF_simple
  ι := CandidateEulerIndex
  ι_infinite := inferInstance
  ℓ := candidateEulerLog
  Ω₀ := 1
  c2_intrinsic := candidateC2_intrinsic
  c2_analyticAt := candidateC2_analyticAt
  c2_zero_free := candidateC2_zero_free
  c2_summable := candidateC2_summable
  c2_euler := candidateC2_euler
  c2_locMajorant := candidateC2_locMajorant
  m := 0
  Rfac := zetaRfac
  gfac := zetaGfac
  genus := candidateGenus
  sphereZero := candidateSphereZero
  c3_R_intrinsic := zetaRfac_intrinsic
  c3_R_entire := zetaRfac_entire
  c3_R_zeros_real := zetaRfac_zeros_real
  c3_g_intrinsic := zetaGfac_intrinsic
  c3_g_entire := zetaGfac_entire
  c3_sphere_nonreal := candidateSphereZero_im_pos
  c3_multipliable := candidateC3_multipliable
  c3_locMajorant := by
    intro z hz
    apply candidateC3_locMajorant z
    simpa using hz
  c3_lowerEdge := candidateC3_lowerEdge
  c3_atN := candidateC3_atN
  c3_factorization := by
    intro z hz
    apply candidateC3_factorization z
    simpa using hz
  c4_infinite := candidateC4_infinite
  valueAtInfinity := ((1 : ℂ) : OnePoint ℂ)
  valueAtInfinity_real := by
    intro z hz
    have h1 : (1 : ℂ) = z := OnePoint.coe_eq_coe.mp hz
    rw [← h1]
    exact Complex.one_im

theorem candidateSection_not_concentric :
    ¬ ∃ c : ℝ, ∀ n : ℕ, (candidateSection.sphereZero n).re = c := by
  change ¬ ∃ c : ℝ, ∀ n : ℕ, (candidateSphereZero n).re = c
  exact candidate_not_concentric

theorem current_ASection_concentricity_type_false :
    ¬ ∀ A : ASection, ∃ c : ℝ, ∀ n : ℕ, (A.sphereZero n).re = c := by
  intro h
  exact candidateSection_not_concentric (h candidateSection)

/-- The countermodel, at the predicate used by the corollary layer. -/
theorem candidateSection_not_concentricASection :
    ¬ ConcentricASection candidateSection := by
  intro h
  exact candidateSection_not_concentric h

/-- The certified reads of the countermodel are not pairwise equal either:
the two formulations agree (`concentricASection_iff_pairwiseTransportLevel`),
so the singleton component cannot be supplying read equality in general. -/
theorem candidateSection_not_pairwiseTransportLevel :
    ¬ PairwiseTransportLevel candidateSection := by
  intro h
  exact candidateSection_not_concentricASection
    ((concentricASection_iff_pairwiseTransportLevel candidateSection).mpr h)

end SpecCandidate
