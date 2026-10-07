import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Define the upper half-plane topology component (y > 0)
def Hyperbolic2Space : Type := { p : ℝ × ℝ // 0 < p.2 }

namespace Hyperbolic2Space

section

open Real MeasureTheory intervalIntegral

/-- The integrand for hyperbolic arc-length at time t along curve γ:
      √(x'(t)² + y'(t)²) / y(t) -/
private noncomputable def hypSpeedAt (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  let v := deriv γ t
  sqrt (v.1 ^ 2 + v.2 ^ 2) / (γ t).2

/-- **Hyperbolic length** of a curve γ : [a, b] → ℍ²:

      l_hyp(γ) = ∫_a^b  √(x'(t)² + y'(t)²) / y(t)  dt  -/
noncomputable def hypLength (γ : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, hypSpeedAt γ t

end

end Hyperbolic2Space

/-
  HyperbolicSpace.lean

  A starting scaffold for formalizing hyperbolic 3-space H^3, following
  §1.1 of R. E. Schwartz, "Mostow Rigidity Made Easier" (arXiv:2512.09774).

  MODELING CHOICE:
  Rather than building H^3 from the Riemannian metric ds^2 = (dx^2+dy^2+dt^2)/t^2
  and deriving distance via geodesic length-minimization (which would require
  calculus-of-variations machinery not readily available in Mathlib), we take
  the standard closed-form distance formula on the upper half-space model as
  the DEFINITION of the metric. This is mathematically equivalent to the
  Riemannian definition, and it is the form you actually need to prove F1-F4.

    d((z1,t1),(z2,t2)) = arccosh( 1 + (|z1-z2|^2 + (t1-t2)^2) / (2*t1*t2) )

  Schwartz identifies H^3 with C x (0,∞); we do the same, as a subtype.
-/


noncomputable section
open Complex Real

/-- Points of hyperbolic 3-space, as pairs (z, t) with z : C, t > 0. -/
def H3 : Type := {p : ℂ × ℝ // 0 < p.2}

namespace H3

instance : CoeSort H3 (ℂ × ℝ) := ⟨fun p => p.1⟩

/-- The complex ("horizontal") coordinate of a point of H3. -/
def z (p : H3) : ℂ := p.1.1

/-- The height ("vertical") coordinate of a point of H3; always positive. -/
def t (p : H3) : ℝ := p.1.2

lemma t_pos (p : H3) : 0 < p.t := p.2

/-- Constructor: build a point of H3 from z : ℂ and t : ℝ with a proof t > 0. -/
def mk (z : ℂ) (t : ℝ) (ht : 0 < t) : H3 := ⟨(z, t), ht⟩

@[simp] lemma mk_z (z : ℂ) (t : ℝ) (ht : 0 < t) : (mk z t ht).z = z := rfl
@[simp] lemma mk_t (z : ℂ) (t : ℝ) (ht : 0 < t) : (mk z t ht).t = t := rfl

/-- The "arccosh argument" appearing in the closed-form hyperbolic distance
    formula for the upper half-space model. -/
def coshArg (p q : H3) : ℝ :=
  1 + (‖p.z - q.z‖ ^ 2 + (p.t - q.t) ^ 2) / (2 * p.t * q.t)

lemma one_le_coshArg (p q : H3) : 1 ≤ coshArg p q := by
  have htp := p.t_pos
  have htq := q.t_pos
  unfold coshArg
  have hnum : 0 ≤ ‖p.z - q.z‖ ^ 2 + (p.t - q.t) ^ 2 := by positivity
  have hden : 0 < 2 * p.t * q.t := by positivity
  nlinarith [div_nonneg hnum hden.le]

/-- **NOTE:** Mathlib provides `Real.arsinh` (since `sinh` is bijective on all
    of `ℝ`) but does *not* provide `Real.arccosh`, because `cosh` is only
    injective once you restrict its domain to `[0, ∞)`. We define our own
    version here, following exactly the same logarithmic-formula style Mathlib
    uses for `arsinh`, restricted in meaning to `x ≥ 1` (the only range we
    ever apply it to, via `one_le_coshArg`). -/
def arccosh (x : ℝ) : ℝ := Real.log (x + Real.sqrt (x ^ 2 - 1))

lemma arccosh_one : arccosh 1 = 0 := by
  unfold arccosh
  have h0 : (1 : ℝ) ^ 2 - 1 = 0 := by ring
  rw [h0, Real.sqrt_zero, add_zero, Real.log_one]

lemma arccosh_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ arccosh x := by
  unfold arccosh
  apply Real.log_nonneg
  nlinarith [Real.sqrt_nonneg (x ^ 2 - 1)]

/-- `arccosh x = 0` exactly at `x = 1`, for `x ≥ 1`. This is the analytic fact
    behind "identity of indiscernibles" for `dist`: it says the only way the
    logarithm collapses to `0` is if its argument was already `1`. We prove
    this directly from `Real.log_pos` (confirmed to exist in Mathlib, unlike
    a hypothetical `Real.log_eq_zero_iff`) rather than a general "log = 0 iff
    arg = 1" lemma. -/
lemma arccosh_eq_zero_iff {x : ℝ} (hx : 1 ≤ x) : arccosh x = 0 ↔ x = 1 := by
  constructor
  · intro h
    by_contra hne
    have hgt : 1 < x := lt_of_le_of_ne hx (Ne.symm hne)
    have harg : 1 < x + Real.sqrt (x ^ 2 - 1) := by
      have hsq := Real.sqrt_nonneg (x ^ 2 - 1)
      linarith
    have hpos : 0 < arccosh x := by
      unfold arccosh
      exact Real.log_pos harg
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  · intro h
    subst h
    exact arccosh_one

/-- `coshArg p q = 1` exactly when `p = q`. This is the geometric heart of
    "identity of indiscernibles": the closed-form distance formula only
    collapses to its minimum value `1` when both the complex coordinate and
    the height coordinate agree. -/
lemma coshArg_eq_one_iff (p q : H3) : coshArg p q = 1 ↔ p = q := by
  have htp := p.t_pos
  have htq := q.t_pos
  unfold coshArg
  constructor
  · intro h
    have hden : (0 : ℝ) < 2 * p.t * q.t := by positivity
    have hfrac : (‖p.z - q.z‖ ^ 2 + (p.t - q.t) ^ 2) / (2 * p.t * q.t) = 0 := by
      linarith
    have hsum : ‖p.z - q.z‖ ^ 2 + (p.t - q.t) ^ 2 = 0 := by
      rcases (div_eq_zero_iff).mp hfrac with h1 | h1
      · exact h1
      · exact absurd h1 (ne_of_gt hden)
    have hz2 : ‖p.z - q.z‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg (p.t - q.t), sq_nonneg ‖p.z - q.z‖]
    have ht2 : (p.t - q.t) ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖p.z - q.z‖]
    have hz : p.z = q.z := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz2))
    have ht : p.t = q.t := sub_eq_zero.mp (sq_eq_zero_iff.mp ht2)
    exact Subtype.ext (Prod.ext hz ht)
  · intro h
    subst h
    simp

/-- Hyperbolic distance on H3, via the closed-form upper-half-space formula. -/
def dist (p q : H3) : ℝ := arccosh (coshArg p q)

@[simp] lemma dist_self (p : H3) : dist p p = 0 := by
  unfold dist
  rw [arccosh_eq_zero_iff (one_le_coshArg p p)]
  exact (coshArg_eq_one_iff p p).mpr rfl

lemma dist_symm (p q : H3) : dist p q = dist q p := by
  unfold dist coshArg
  rw [norm_sub_rev]
  ring_nf

lemma dist_nonneg (p q : H3) : 0 ≤ dist p q := by
  unfold dist
  exact arccosh_nonneg (one_le_coshArg p q)

/-- **The key upgrade you flagged**: `dist p q = 0` if and only if `p = q`.
    This is exactly the "identity of indiscernibles" axiom that turns a mere
    `PseudoMetricSpace` into a genuine `MetricSpace`. -/
lemma dist_eq_zero_iff (p q : H3) : dist p q = 0 ↔ p = q := by
  unfold dist
  rw [arccosh_eq_zero_iff (one_le_coshArg p q)]
  exact coshArg_eq_one_iff p q

/-- Distinct points are at strictly positive distance. -/
lemma dist_pos {p q : H3} (h : p ≠ q) : 0 < dist p q := by
  rcases (dist_nonneg p q).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd ((dist_eq_zero_iff p q).mp heq.symm) h


-- ================= bookkeeping helpers =================

/-- The one fact that replaces `sq_eq_sq`-type lemmas whose exact name churns:
    derived from nothing but `Real.sqrt_sq`, so it can't go stale. -/
lemma eq_of_sq_eq_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  have := congrArg Real.sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at this

lemma sinh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

lemma sqrt_mul_sqrt_eq {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 ≤ z) :
    Real.sqrt (x * y) * Real.sqrt (y * z) = y * Real.sqrt (x * z) := by
  apply eq_of_sq_eq_sq_of_nonneg (by positivity) (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
  ring

noncomputable def amb (p : H3) : EuclideanSpace ℝ (Fin 3) :=
  !₂[p.z.re, p.z.im, p.t]

noncomputable def reflect (p : H3) : EuclideanSpace ℝ (Fin 3) :=
  !₂[p.z.re, p.z.im, -p.t]

@[simp] lemma amb_dist_sq (p q : H3) :
    Dist.dist p.amb q.amb ^ 2
      = (p.z.re - q.z.re) ^ 2 + (p.z.im - q.z.im) ^ 2 + (p.t - q.t) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [amb, Real.dist_eq];

@[simp] lemma reflect_dist_sq (p q : H3) :
    Dist.dist p.amb q.reflect ^ 2
      = (p.z.re - q.z.re) ^ 2 + (p.z.im - q.z.im) ^ 2 + (p.t + q.t) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [amb, reflect, Real.dist_eq];

lemma self_reflect_dist (p : H3) : Dist.dist p.amb p.reflect = 2 * p.t := by
  apply eq_of_sq_eq_sq_of_nonneg (by positivity) (by linarith [p.t_pos])
  rw[reflect_dist_sq p p]
  ring

-- `dist p q` unfolds to `Real.arccosh (coshArg p q)`; you already have `one_le_coshArg`.
/-- `Real.cosh (arccosh x) = x` for `x ≥ 1` — the defining property of *our*
    `arccosh`. (There's no `Real.cosh_arccosh` to borrow from Mathlib, since
    Mathlib has no `Real.arccosh` at all — see the note above.) -/
lemma cosh_arccosh {x : ℝ} (hx : 1 ≤ x) : Real.cosh (arccosh x) = x := by
  unfold arccosh
  have hsqrt_nonneg : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
  have hy_pos : 0 < x + Real.sqrt (x ^ 2 - 1) := by linarith
  have hy_ne : (x + Real.sqrt (x ^ 2 - 1)) ≠ 0 := hy_pos.ne'
  have hsq_eq : Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg (x - 1)])
  rw [Real.cosh_eq, Real.exp_log hy_pos, Real.exp_neg, Real.exp_log hy_pos]
  field_simp
  nlinarith [hsq_eq]

lemma cosh_dist (p q : H3) : Real.cosh (dist p q) = coshArg p q := by
  unfold dist
  exact cosh_arccosh (one_le_coshArg p q)

lemma sinh_half_dist (p q : H3) :
    Real.sinh (dist p q / 2) = Dist.dist p.amb q.amb / (2 * Real.sqrt (p.t * q.t)) := by
  have hpq : (0:ℝ) < p.t * q.t := mul_pos p.t_pos q.t_pos
  apply eq_of_sq_eq_sq_of_nonneg
    (sinh_nonneg_of_nonneg (by linarith [dist_nonneg p q])) (by positivity)
  have hpyth : Real.cosh (dist p q) = 1 + 2 * Real.sinh (dist p q / 2) ^ 2 := by
    have h := Real.cosh_add (dist p q / 2) (dist p q / 2)
    rw [show dist p q / 2 + dist p q / 2 = dist p q by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (dist p q / 2), h]
  rw [cosh_dist p q] at hpyth
  have hArg : coshArg p q = 1 + Dist.dist p.amb q.amb ^ 2 / (2 * p.t * q.t) := by
    rw [amb_dist_sq p q]
    unfold coshArg
    have hnorm : ‖p.z - q.z‖ ^ 2 = (p.z.re - q.z.re) ^ 2 + (p.z.im - q.z.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    rw [hnorm]
  rw [hArg] at hpyth
  rw [div_pow, mul_pow, Real.sq_sqrt hpq.le]
  have hsinh_sq : Real.sinh (dist p q / 2) ^ 2
    = Dist.dist p.amb q.amb ^ 2 / (2 * p.t * q.t) / 2 := by
    linarith [hpyth]
  rw [hsinh_sq]
  ring

lemma cosh_half_dist (p q : H3) :
    Real.cosh (dist p q / 2) = Dist.dist p.amb q.reflect / (2 * Real.sqrt (p.t * q.t)) := by
  have hpq : (0:ℝ) < p.t * q.t := mul_pos p.t_pos q.t_pos
  apply eq_of_sq_eq_sq_of_nonneg (Real.cosh_pos _).le (by positivity)
  have hpyth : Real.cosh (dist p q / 2) ^ 2 = 1 + Real.sinh (dist p q / 2) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (dist p q / 2)]
  have hsinh2 : Real.sinh (dist p q / 2) ^ 2
      = Dist.dist p.amb q.amb ^ 2 / (4 * (p.t * q.t)) := by
    rw [sinh_half_dist, div_pow, mul_pow, Real.sq_sqrt hpq.le]; ring
  rw [hpyth, hsinh2, div_pow, mul_pow, Real.sq_sqrt hpq.le,
      reflect_dist_sq p q, amb_dist_sq p q]
  field_simp [p.t_pos.ne', q.t_pos.ne']
  ring


lemma sinh_half_dist_add_dist (a b c : H3) :
    Real.sinh ((dist a b + dist b c) / 2)
      = (Dist.dist a.amb b.amb * Dist.dist c.amb b.reflect + Dist.dist a.amb b.reflect *
          Dist.dist b.amb c.amb) / (4 * b.t * Real.sqrt (a.t * c.t)) := by
  rw[dist_symm b c]
  have key : Real.sqrt (a.t * b.t) * Real.sqrt (c.t * b.t) = b.t * Real.sqrt (a.t * c.t) := by
    rw [mul_comm c.t b.t]
    exact sqrt_mul_sqrt_eq a.t_pos.le b.t_pos c.t_pos.le
  rw [show (dist a b + dist c b) / 2 = dist a b / 2 + dist c b / 2 by ring, Real.sinh_add,
      sinh_half_dist, cosh_half_dist, cosh_half_dist, sinh_half_dist]
  rw [div_mul_div_comm, div_mul_div_comm,
      show (2) * Real.sqrt (a.t*b.t) * (2 * Real.sqrt (c.t*b.t))
         = 4 * (Real.sqrt (a.t*b.t) * Real.sqrt (c.t*b.t)) by ring,
      key]
  rw[dist_comm b.amb c.amb]
  ring


theorem dist_triangle (a b c : H3) : dist a c ≤ dist a b + dist b c := by
  have hS : (0:ℝ) < Real.sqrt (a.t * c.t) := Real.sqrt_pos.mpr (mul_pos a.t_pos c.t_pos)
  have hptolemy : Dist.dist a.amb c.amb * (2 * b.t)
      ≤ Dist.dist a.amb b.amb * Dist.dist c.amb b.reflect + Dist.dist b.amb c.amb *
        Dist.dist a.amb b.reflect := by
    rw [← self_reflect_dist b]
    exact EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist a.amb b.amb c.amb b.reflect
  have hstep : Real.sinh (dist a c / 2) ≤ Real.sinh ((dist a b + dist b c) / 2) := by
    have hbt := b.t_pos
    rw [sinh_half_dist, sinh_half_dist_add_dist, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hptolemy hS.le]
  linarith [Real.sinh_strictMono.le_iff_le.mp hstep]


/-- Package `H3` as a genuine `MetricSpace` — not just a `PseudoMetricSpace` —
    since `eq_of_dist_eq_zero` is now available via `dist_eq_zero_iff`. This
    is modulo the triangle inequality above. Mathlib automatically derives
    the underlying `PseudoMetricSpace H3` instance from this one, so all
    pseudometric-level API remains available too. -/
instance : MetricSpace H3 where
  dist := dist
  dist_self := dist_self
  dist_comm := dist_symm
  dist_triangle := dist_triangle
  eq_of_dist_eq_zero := fun {p q} h => (dist_eq_zero_iff p q).mp h
  -- `edist` and `edist_dist` are deliberately omitted: both have built-in
  -- Mathlib defaults (`edist := fun x y => ENNReal.ofReal (dist x y)` and
  -- `edist_dist := by intros; rfl`) that are designed to be used as-is.
  -- Restating `edist_dist` explicitly can force premature unfolding that
  -- breaks the `rfl` proof, as happened above; simply omit it.
end H3

/-! ### Isometries of H3

Schwartz's `F1`: for `a ≠ 0` in `ℂ` and `b : ℂ`, the map
`(z,t) ↦ (a*z + b, |a|*t)` is an isometry of `H3`.
-/

namespace H3

/-- The similarity map `(z,t) ↦ (a*z + b, |a|*t)` on H3, for `a ≠ 0`. -/
def similarity (a b : ℂ) (ha : a ≠ 0) : H3 → H3 :=
  fun p => mk (a * p.z + b) (‖a‖ * p.t) (by
    have := p.t_pos
    have habs : 0 < ‖a‖ := by simpa using ha
    positivity)

/-- **F1.** When `a ≠ 0`, the map `(z,t) ↦ (az+b, |a|t)` acts isometrically on H3. -/
theorem F1_isometry (a b : ℂ) (ha : a ≠ 0) (p q : H3) :
    dist (similarity a b ha p) (similarity a b ha q) = dist p q := by
  unfold dist coshArg similarity
  simp only [mk_z, mk_t]
  congr 1
  have habs : 0 < ‖a‖ := by simpa using ha
  have hp := p.t_pos
  have hq := q.t_pos
  have hdiff : a * p.z + b - (a * q.z + b) = a * (p.z - q.z) := by ring
  rw [hdiff, norm_mul]
  field_simp [habs.ne', hp.ne', hq.ne']

/-! ### F2: Geodesics are vertical rays or semicircles -/

/-- A curve `γ : ℝ → H3` is a geodesic (isometric embedding) if for all
    parameter values `s u`, the hyperbolic distance equals `|s - u|`. -/
def IsGeodesic (γ : ℝ → H3) : Prop :=
  ∀ s u : ℝ, dist (γ s) (γ u) = |s - u|

/-- The vertical ray `{z0} × (0,∞)` parametrized by arc-length: `s ↦ (z0, eˢ)`.
    The exponential parametrization is correct because the hyperbolic speed of
    `s ↦ (z0, eˢ)` equals 1: ds_hyp = dt/t = eˢ ds / eˢ = ds. -/
def verticalGeodesic (z0 : ℂ) : ℝ → H3 :=
  fun s => mk z0 (Real.exp s) (Real.exp_pos s)

/-- Helper: `arccosh (cosh x) = x` for `x ≥ 0`.
    Needed to close the vertical geodesic proof.
`arccosh (cosh x) = x` for `x ≥ 0`. -/
lemma arccosh_cosh {x : ℝ} (hx : 0 ≤ x) : arccosh (Real.cosh x) = x := by
  unfold arccosh
  have hsinh_nn : 0 ≤ Real.sinh x := sinh_nonneg_of_nonneg hx
  have hsqrt : Real.sqrt (Real.cosh x ^ 2 - 1) = Real.sinh x := by
    have : Real.sinh x ^ 2 = Real.cosh x ^ 2 - 1 :=
      by nlinarith [Real.cosh_sq_sub_sinh_sq x]
    rw [← this]; exact Real.sqrt_sq hsinh_nn
  rw [hsqrt, Real.cosh_add_sinh, Real.log_exp]


/-- **F2 (vertical case).** The vertical ray `s ↦ (z0, eˢ)` is a geodesic:
    `dist (z0, eˢ) (z0, eᵘ) = |s - u|` for all `s u : ℝ`. -/
theorem F2_vertical_is_geodesic (z0 : ℂ) : IsGeodesic (verticalGeodesic z0) := by
  intro s u
  unfold verticalGeodesic dist coshArg
  simp only [mk_z, mk_t, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add]
  -- Goal: arccosh (1 + (exp s - exp u)² / (2 * exp s * exp u)) = |s - u|
  -- Step 1: show the arccosh argument equals cosh(s - u)
  have key : 1 + (Real.exp s - Real.exp u) ^ 2 / (2 * Real.exp s * Real.exp u)
           = Real.cosh (s - u) := by
    have hs : Real.exp s > 0 := Real.exp_pos s
    have hu : Real.exp u > 0 := Real.exp_pos u
    rw [Real.cosh_sub, Real.cosh_eq s, Real.cosh_eq u,
        Real.sinh_eq s, Real.sinh_eq u,
        Real.exp_neg s, Real.exp_neg u]
    field_simp
    ring
  -- Step 2: arccosh (cosh (s - u)) = |s - u|
  rw [key, ← Real.cosh_abs]
  exact arccosh_cosh (abs_nonneg _)



/-- The image of a geodesic set in the boundary picture (ℝ × (0,∞)) is either
    a vertical ray or a semicircle meeting ℝ × {0} at right angles. -/
def IsGeodesicSet (S : Set (ℝ × ℝ)) : Prop :=
  -- vertical ray: { (c, y) | y > 0 }
  (∃ c : ℝ, S = {p : ℝ × ℝ | p.1 = c ∧ 0 < p.2}) ∨
  -- semicircle of radius r centred at (a, 0): meets boundary at right angles
  (∃ (a r : ℝ), 0 < r ∧ S = {p : ℝ × ℝ | (p.1 - a) ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 < p.2})

/-! ### F3: Hyperbolic vs Euclidean arc-length on C × [a, b] -/

/-- Euclidean speed of a curve `γ : ℝ → H3` at parameter `t`:
    the norm of the derivative treating H3 ⊂ ℝ³. -/
noncomputable def euclidSpeed (γ : ℝ → H3) (t : ℝ) : ℝ :=
  Real.sqrt ((deriv (fun s => (γ s).z.re) t) ^ 2 +
             (deriv (fun s => (γ s).z.im) t) ^ 2 +
             (deriv (fun s => (γ s).t)    t) ^ 2)

/-- Hyperbolic speed of a curve `γ : ℝ → H3` at parameter `t`:
    Euclidean speed divided by the height `(γ t).t`. -/
noncomputable def hypSpeed (γ : ℝ → H3) (t : ℝ) : ℝ :=
  euclidSpeed γ t / (γ t).t

/-- Euclidean speed is always nonneg (it is a `Real.sqrt`). -/
lemma euclidSpeed_nonneg (γ : ℝ → H3) (t : ℝ) : 0 ≤ euclidSpeed γ t :=
  Real.sqrt_nonneg _

/-- Hyperbolic speed is always nonneg. -/
lemma hypSpeed_nonneg (γ : ℝ → H3) (t : ℝ) : 0 ≤ hypSpeed γ t :=
  div_nonneg (euclidSpeed_nonneg γ t) (γ t).t_pos.le

/-- Key pointwise identity: euclidSpeed = height × hypSpeed. -/
lemma euclidSpeed_eq (γ : ℝ → H3) (t : ℝ) :
    euclidSpeed γ t = (γ t).t * hypSpeed γ t := by
  unfold hypSpeed
  rw [mul_div_cancel₀]
  exact (γ t).t_pos.ne'

/-- **F3.** On the slab C × [a, b] (heights between `a` and `b`), hyperbolic
    and Euclidean arc-length satisfy `a · ℓ_hyp ≤ ℓ_E ≤ b · ℓ_hyp`. -/
theorem F3_arc_length_comparison (γ : ℝ → H3) (s₁ s₂ : ℝ) (hs : s₁ ≤ s₂)
    (a b : ℝ) (_ha : 0 < a) (_hab : a ≤ b)
    (hγ_lower : ∀ t ∈ Set.Icc s₁ s₂, a ≤ (γ t).t)
    (hγ_upper : ∀ t ∈ Set.Icc s₁ s₂, (γ t).t ≤ b)
    -- use IntervalIntegrable, NOT MeasureTheory.Integrable
    (hS_hyp  : IntervalIntegrable (fun t => hypSpeed γ t)
                 MeasureTheory.volume s₁ s₂)
    (hS_eucl : IntervalIntegrable (fun t => euclidSpeed γ t)
                 MeasureTheory.volume s₁ s₂) :
    (a * ∫ t in s₁..s₂, hypSpeed γ t ≤ ∫ t in s₁..s₂, euclidSpeed γ t) ∧
    (∫ t in s₁..s₂, euclidSpeed γ t ≤ b * ∫ t in s₁..s₂, hypSpeed γ t) := by
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hs (hS_hyp.const_mul a) hS_eucl
    intro t ht
    rw [euclidSpeed_eq]
    exact mul_le_mul_of_nonneg_right (hγ_lower t ht) (hypSpeed_nonneg γ t)
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hs hS_eucl (hS_hyp.const_mul b)
    intro t ht
    rw [euclidSpeed_eq]
    exact mul_le_mul_of_nonneg_right (hγ_upper t ht) (hypSpeed_nonneg γ t)



/-! ### F4: Nearest-point projection to the vertical axis -/

/-- The vertical axis γ = {0} × (0,∞) in H3. -/
def axis : Set H3 := {p | p.z = 0}

/-- The map φ(p) = (0, ‖p‖_ℝ³) sending p = (z,t) to the point on the axis
    nearest to p, where ‖p‖_ℝ³ = √(‖z‖² + t²) is the Euclidean norm in ℝ³. -/
def phi (p : H3) : H3 :=
    mk 0 (Real.sqrt (‖p.z‖ ^ 2 + p.t ^ 2)) (by
    apply Real.sqrt_pos_of_pos
    have h1 : 0 ≤ ‖p.z‖ ^ 2 := sq_nonneg _
    have h2 : 0 < p.t ^ 2 := sq_pos_of_pos p.t_pos
    linarith)

/-- φ(p) always lies on the axis. -/
theorem F4_phi_mem_axis (p : H3) : phi p ∈ axis := rfl

/-- **F4 (distance bound).** For t ∈ (0,1), the hyperbolic distance from
    (1, t) to the axis γ is less than ln(1/t) + 1. -/
theorem F4_distance_bound (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    dist (mk 1 t ht0) (phi (mk 1 t ht0)) < Real.log (1 / t) + 1 := by
  -- Set r = √(1 + t²), the Euclidean norm of (1, t).
  set r := Real.sqrt (1 + t ^ 2) with hr_def
  have hr_pos : 0 < r := Real.sqrt_pos_of_pos (by nlinarith [sq_nonneg t])
  have hr_sq  : r ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg t])
  -- Step 1: phi(mk 1 t ht0) = mk 0 r hr_pos
  have hphi : phi (mk 1 t ht0) = mk 0 r hr_pos := by
    unfold phi
    simp only [mk_z, mk_t, norm_one, one_pow]
    norm_num [hr_def]
  rw [hphi]
  -- Step 2: coshArg (mk 1 t) (mk 0 r) = r / t
  have hcosh : coshArg (mk 1 t ht0) (mk 0 r hr_pos) = r / t := by
    unfold coshArg
    simp only [mk_z, mk_t, sub_zero, norm_one]
    field_simp
    nlinarith [hr_sq]
  -- Step 3: arccosh(r/t) = log((r + 1)/t)
  unfold dist
  rw [hcosh]
  have harccosh : arccosh (r / t) = Real.log ((r + 1) / t) := by
    unfold arccosh
    have hsq : (r / t) ^ 2 - 1 = (1 / t) ^ 2 := by
      field_simp; nlinarith [hr_sq]
    rw [hsq, Real.sqrt_sq (by positivity)]
    congr 1; ring
  rw [harccosh]
  -- Step 4: log((r+1)/t) < log(1/t) + 1  ⟺  log(r+1) < 1
  -- Rewrite log((r+1)/t) = log(r+1) - log t
  -- and    log(1/t)      = -log t = 0 - log t
  -- so goal becomes: log(r+1) - log t < -log t + 1
  -- which simplifies to: log(r+1) < 1
  rw [Real.log_div (by linarith) ht0.ne',
      Real.log_div (by norm_num) ht0.ne', Real.log_one]
    -- Goal: Real.log (r + 1) - Real.log t < -Real.log t + 1
  suffices h : Real.log (r + 1) < 1 by linarith
  -- log(r+1) < 1 ⟺ r+1 < exp 1
  rw [Real.log_lt_iff_lt_exp (by linarith)]
  -- Goal: r + 1 < exp 1
  have hr_lt_sqrt2 : r < Real.sqrt 2 := by
    apply Real.sqrt_lt_sqrt (by nlinarith [sq_nonneg t])
    nlinarith [sq_nonneg t]
  have hsqrt2_lt : Real.sqrt 2 < Real.exp 1 - 1 := by
    have hs : Real.sqrt 2 < 1.42 := by
      have : (1.42 : ℝ) = Real.sqrt (1.42 ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
      rw [this]
      apply Real.sqrt_lt_sqrt (by norm_num)
      norm_num
    have he : (2.42 : ℝ) < Real.exp 1 := by
      have h1 : Real.exp (1/4 : ℝ) ≥ 5/4 := by
        have := Real.add_one_le_exp (1/4 : ℝ); linarith
      have h2 : Real.exp 1 = Real.exp (1/4) ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hpos : (0 : ℝ) < Real.exp (1/4) := Real.exp_pos _
      have h3 : Real.exp (1/4) ^ 2 ≥ 25/16 := by nlinarith
      have h4 : Real.exp (1/4) ^ 4 ≥ 625/256 := by
        nlinarith [sq_nonneg (Real.exp (1/4) ^ 2)]
      linarith
    linarith
  linarith
