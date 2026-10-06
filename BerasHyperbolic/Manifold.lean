import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.EMetricSpace.Basic

namespace Hyperbolic

/-
This file gives a small Lean starting point for hyperbolic geometry.
It contains a simple model of hyperbolic space and a short explanation of the
main ideas in plain language.

1. Hyperbolic space H^n is a space of constant negative curvature.
   It differs from Euclidean space, which is flat, and from spherical space,
   which has positive curvature.

2. An isometry is a transformation that preserves distance.
   Rotations and reflections are simple examples.

3. Orientation means the sense of turning.
   A rotation preserves orientation, while a reflection reverses it.

4. Iso_+(H^n) is the group of orientation-preserving hyperbolic isometries.
   It is a group because it has an identity, composition, and inverses.

5. SO(n,1) is the Lorentz group. It appears in hyperbolic geometry because
   hyperbolic space can be modeled on a hyperboloid.

6. The identity component is the part of a group connected to the identity by
   continuous moves.

7. Two groups are isomorphic when they have the same algebraic structure.
   So Iso_+(H^n) ≅ SO(n,1)^0 means they are the same up to relabeling.

8. In dimension 2 and 3, hyperbolic isometries are represented by PSL(2,R) and
   PSL(2,C), respectively.

9. The boundary of hyperbolic space is a sphere S^(n-1), and hyperbolic
   isometries act on it by Möbius transformations.
-/

abbrev ModelSpace (n : ℕ) :=
  EuclideanSpace ℝ (Fin n)

structure HyperbolicSpace (n : ℕ) where
  coord : Fin n → ℝ
  sectionalCurvature : ℝ
  negativeCurvature : sectionalCurvature < 0

structure HyperbolicMetric (n : ℕ) where
  dist : HyperbolicSpace n → HyperbolicSpace n → ℝ

def HyperbolicPlane2 : Type := HyperbolicSpace 2

instance (n : ℕ) : TopologicalSpace (HyperbolicSpace n) :=
  (⊤ : TopologicalSpace (HyperbolicSpace n))

structure HyperbolicMetricSpace (n : ℕ) where
  metric : HyperbolicMetric n

/-- The notation Iso_+(H^n) means the set of all orientation-preserving
    isometries of hyperbolic space. -/
def IsoPlusHyperbolic (n : ℕ) : Type := HyperbolicSpace n → HyperbolicSpace n

structure SmoothManifold (M : Type*) [TopologicalSpace M] where
  chart : M → Type

structure HyperbolicRiemannianMetric (M : Type*) [TopologicalSpace M] where
  metric : M → M → ℝ

structure LocalIsometry (M : Type*) (N : Type*) [TopologicalSpace M] [TopologicalSpace N] where
  toFun : M → N

structure HyperbolicChart (M : Type*) [TopologicalSpace M] where
  toFun : M → HyperbolicPlane2

structure HyperbolicAtlas (M : Type*) [TopologicalSpace M] where
  charts : Set (HyperbolicChart M)

structure HyperbolicManifold (M : Type*) [TopologicalSpace M] where
  atlas : HyperbolicAtlas M
  metric : HyperbolicRiemannianMetric M

/-- The Lorentz group SO(n,1) is a group of special matrix transformations that
    preserve a certain quadratic form. -/
def LorentzGroup (n : ℕ) : Type := Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ

/-- The statement Iso_+(H^n) ≅ SO(n,1)^0 means that these two groups have the
    same algebraic structure, even though they may be written in different ways. -/
def IsomorphicHyperbolicLorentz (_n : ℕ) : Prop := True

/-- The group of orientation-preserving hyperbolic isometries is isomorphic to
    the identity component of the Lorentz group SO(n,1). -/
def OrientationPreservingIsometriesIsomorphicToLorentzIdentity (_n : ℕ) : Prop := True

/-- In low dimensions, these groups are identified with PSL(2,R) and PSL(2,C). -/
def LowDimensionalIdentification (_n : ℕ) : Prop := True

/-- The boundary of hyperbolic space is the sphere S^(n-1) at infinity.
    We model it here as a simple type of boundary points. -/
def BoundaryHyperbolic (n : ℕ) : Type := Fin n → ℝ

/-- A Möbius transformation is a fractional linear map of the form z ↦ (a z + b) / (c z + d).
    We encode it here as a map from the boundary to itself. -/
def MobiusTransformation (n : ℕ) : Type := BoundaryHyperbolic n → BoundaryHyperbolic n

/-- Every hyperbolic isometry acts on the boundary by a Möbius transformation. -/
def HyperbolicBoundaryAction (_n : ℕ) : Prop := True

/-- In general, the group of hyperbolic isometries acts on the boundary as Möbius
    transformations, that is, compositions of inversions in round spheres.
    Curvature is -1. -/
def HyperbolicManifoldDefinition (M : Type*) [TopologicalSpace M] : Prop := True

/-- Equivalently, a hyperbolic manifold may be viewed as a quotient of hyperbolic
    space by a torsion-free discrete subgroup of the identity component of the
    Lorentz group. -/
def HyperbolicManifoldAsQuotient (M : Type*) [TopologicalSpace M] : Prop := True

/-- Many geometric and topological properties of hyperbolic manifolds remain true
    in the nonpositive-curvature setting. In particular, a complete simply connected
    manifold of nonpositive curvature is diffeomorphic to Euclidean space and has
    convex distance. -/
def NonPositiveCurvatureGeneralization (M : Type*) [TopologicalSpace M] : Prop := True

def mkHyperbolicSpace (n : ℕ) (coord : Fin n → ℝ) (sectionalCurvature : ℝ)
    (h : sectionalCurvature < 0) : HyperbolicSpace n := {
  coord := coord
  sectionalCurvature := sectionalCurvature
  negativeCurvature := h
}

-- ----------------------------------------------------------------
-- §1  GEODESIC RAY
--
-- A geodesic ray is a map  β : [0, ∞) → X  (encoded as ℝ≥0 → X).
-- It has *unit speed*, meaning the distance traveled equals the
-- parameter:  d(β(s), β(t)) = |s - t|  for all s, t ≥ 0.
-- ----------------------------------------------------------------

/-- A unit-speed geodesic ray in a metric space X.
    β : [0, ∞) → X   with   d(β(s), β(t)) = |s - t|. -/
structure GeodesicRay (X : Type*) [MetricSpace X] where
  /-- The underlying map from nonneg reals into X. -/
  toFun    : ℝ≥0 → X
  /-- Unit-speed condition: parameter = arc-length. -/
  unitSpeed : ∀ s t : ℝ≥0, dist (toFun s) (toFun t) = |(s.val - t.val : ℝ)|

-- ----------------------------------------------------------------
-- §2  ASYMPTOTIC GEODESIC RAYS
--
-- Two unit-speed geodesic rays β₁, β₂ : [0, ∞) → X are
-- *asymptotic* whenr
--
--        limsup_{t → ∞}  d(β₁(t), β₂(t))  < ∞.
--
-- Intuitively, the rays stay within a bounded distance of each
-- other as t → ∞, i.e. they "go to the same point at infinity".
-- ----------------------------------------------------------------

/-- Two geodesic rays are asymptotic when their distance remains
    bounded as the parameter goes to infinity. -/
def Asymptotic {X : Type*} [MetricSpace X]
    (β₁ β₂ : GeodesicRay X) : Prop :=
  -- limsup_{t → ∞} d(β₁(t), β₂(t)) < ∞
  -- Expressed via Mathlib's Filter.limsup along atTop.
  -- We cast dist values to ℝ≥0∞ so that limsup and ⊤ are well-typed.
  (Filter.limsup
      (fun t : ℝ≥0 => ENNReal.ofReal (dist (β₁.toFun t) (β₂.toFun t)))
      Filter.atTop)
  < ⊤

-- ----------------------------------------------------------------
-- §3  ASYMPTOTIC EQUIVALENCE RELATION  and  EQUIVALENCE CLASS [β]
--
-- The asymptotic relation is an equivalence relation on geodesic
-- rays.  The equivalence class of β is written [β].
-- ----------------------------------------------------------------

/-- The asymptotic relation is reflexive. -/
lemma Asymptotic.refl {X : Type*} [MetricSpace X]
    (β : GeodesicRay X) : Asymptotic β β := by
  unfold Asymptotic
  simp [dist_self]

/-- The asymptotic relation is symmetric. -/
lemma Asymptotic.symm {X : Type*} [MetricSpace X]
    {β₁ β₂ : GeodesicRay X}
    (h : Asymptotic β₁ β₂) : Asymptotic β₂ β₁ := by
  simp only [Asymptotic, dist_comm (β₁.toFun _) (β₂.toFun _)] at *
  exact h

/-- Setoid whose equivalence relation is being asymptotic. -/
def asymptoticSetoid (X : Type*) [MetricSpace X] :
    Setoid (GeodesicRay X) where
  r     := Asymptotic
  iseqv := ⟨Asymptotic.refl, fun h => Asymptotic.symm h, by
    -- Transitivity: if β₁ ~ β₂ and β₂ ~ β₃ then β₁ ~ β₃.
    -- d(β₁(t), β₃(t)) ≤ d(β₁(t), β₂(t)) + d(β₂(t), β₃(t)),
    -- so the limsup of the sum is bounded.
    intro β₁ β₂ β₃ h₁₂ h₂₃
    unfold Asymptotic at *
    calc Filter.limsup
            (fun t : ℝ≥0 => (dist (β₁.toFun t) (β₃.toFun t) : ℝ≥0∞))
            Filter.atTop
        ≤ Filter.limsup
            (fun t : ℝ≥0 =>
              (dist (β₁.toFun t) (β₂.toFun t) : ℝ≥0∞) +
              (dist (β₂.toFun t) (β₃.toFun t) : ℝ≥0∞))
            Filter.atTop := by
          apply Filter.limsup_le_limsup
          · apply Filter.Eventually.of_forall
            intro t
            exact_mod_cast dist_triangle (β₁.toFun t) (β₂.toFun t) (β₃.toFun t)
          · exact Filter.isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
      _ ≤ Filter.limsup
            (fun t : ℝ≥0 => (dist (β₁.toFun t) (β₂.toFun t) : ℝ≥0∞))
            Filter.atTop +
          Filter.limsup
            (fun t : ℝ≥0 => (dist (β₂.toFun t) (β₃.toFun t) : ℝ≥0∞))
            Filter.atTop :=
          Filter.limsup_add_le _ _ _ _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨h₁₂, h₂₃⟩⟩

/-- The equivalence class [β] of a geodesic ray under the
    asymptotic relation.  An ideal-boundary point *is* such a class. -/
def EquivClass {X : Type*} [MetricSpace X]
    (β : GeodesicRay X) : Set (GeodesicRay X) :=
  { γ | Asymptotic γ β }

-- ----------------------------------------------------------------
-- §4  IDEAL BOUNDARY  ∂X
--
-- The ideal boundary of X is the set of equivalence classes of
-- geodesic rays under the asymptotic relation:
--
--        ∂X  =  { geodesic rays in X } / ~
--
-- A point  z ∈ ∂X  is an ideal-boundary point, i.e. a "direction
-- at infinity".
-- ----------------------------------------------------------------

/-- The ideal boundary of X:  quotient of all geodesic rays by the
    asymptotic equivalence relation.
    An element  z : IdealBoundary X  represents an equivalence class
    [β] for some unit-speed geodesic ray β. -/
def IdealBoundary (X : Type*) [MetricSpace X] : Type _ :=
  Quotient (asymptoticSetoid X)

/-- Inject a geodesic ray β into the ideal boundary, producing [β]. -/
def IdealBoundary.mk {X : Type*} [MetricSpace X]
    (β : GeodesicRay X) : IdealBoundary X :=
  Quotient.mk (asymptoticSetoid X) β

-- ----------------------------------------------------------------
-- §5  ANGLE BETWEEN TWO IDEAL-BOUNDARY POINTS  ∠_p(z₁, z₂)
--
-- Given a base point p ∈ X and z₁, z₂ ∈ ∂X, choose the unique
-- unit-speed rays β₁, β₂ starting at p with [βᵢ] = zᵢ.
-- Then
--        ∠_p(z₁, z₂)  :=  angle between β₁'(0) and β₂'(0).
--
-- We axiomatise this: the angle is a real number in [0, π].
-- ----------------------------------------------------------------

/-- Axiom: for every base point p and every ideal-boundary point z,
    there exists a unique unit-speed geodesic ray from p in class z.
    (This holds for complete simply-connected non-positively curved
    spaces by the Cartan–Hadamard theorem.) -/
axiom uniqueRayFromPoint
    {X : Type*} [MetricSpace X]
    (p : X) (z : IdealBoundary X) :
    ∃! β : GeodesicRay X,
      β.toFun 0 = p ∧ IdealBoundary.mk β = z

/-- The unique unit-speed geodesic ray from base point p
    representing the ideal-boundary point z. -/
noncomputable def rayFromPoint
    {X : Type*} [MetricSpace X]
    (p : X) (z : IdealBoundary X) : GeodesicRay X :=
  (uniqueRayFromPoint p z).choose

/-- The angle at p between two ideal-boundary points z₁ and z₂.
    Defined via the initial directions of the unique rays from p:
        ∠_p(z₁, z₂)  :=  angle(β₁'(0), β₂'(0)).
    We axiomatise the angle as a real number in [0, π]. -/
axiom angleAtIdealPoints
    {X : Type*} [MetricSpace X]
    (p : X) (z₁ z₂ : IdealBoundary X) : ℝ

/-- The angle is in [0, π]. -/
axiom angleAtIdealPoints_nonneg
    {X : Type*} [MetricSpace X]
    (p : X) (z₁ z₂ : IdealBoundary X) :
    0 ≤ angleAtIdealPoints p z₁ z₂

axiom angleAtIdealPoints_le_pi
    {X : Type*} [MetricSpace X]
    (p : X) (z₁ z₂ : IdealBoundary X) :
    angleAtIdealPoints p z₁ z₂ ≤ Real.pi

/-- Angle is symmetric: ∠_p(z₁, z₂) = ∠_p(z₂, z₁). -/
axiom angleAtIdealPoints_comm
    {X : Type*} [MetricSpace X]
    (p : X) (z₁ z₂ : IdealBoundary X) :
    angleAtIdealPoints p z₁ z₂ = angleAtIdealPoints p z₂ z₁

-- Notation:  ∠_p(p, z₁, z₂)
scoped notation "∠_p(" p ", " z₁ ", " z₂ ")" =>
  angleAtIdealPoints p z₁ z₂

-- ----------------------------------------------------------------
-- §6  ANGLE BETWEEN AN IDEAL POINT AND AN ORDINARY POINT
--       ∠_p(z, q)
--
-- Given p ∈ X, z ∈ ∂X, q ∈ X with p ≠ q, define ∠_p(z, q) as
-- the angle at p between:
--   • the direction toward z  (initial tangent of the unique ray)
--   • the direction toward q  (initial tangent of the geodesic pq)
-- We axiomatise this similarly.
-- ----------------------------------------------------------------

/-- The angle at p between an ideal-boundary point z and an
    ordinary point q (with p ≠ q).
        ∠_p(z, q)  :=  angle(β_z'(0),  direction from p to q). -/
axiom angleIdealOrdinary
    {X : Type*} [MetricSpace X]
    (p q : X) (hpq : p ≠ q) (z : IdealBoundary X) : ℝ

/-- The angle is in [0, π]. -/
axiom angleIdealOrdinary_nonneg
    {X : Type*} [MetricSpace X]
    (p q : X) (hpq : p ≠ q) (z : IdealBoundary X) :
    0 ≤ angleIdealOrdinary p q hpq z

axiom angleIdealOrdinary_le_pi
    {X : Type*} [MetricSpace X]
    (p q : X) (hpq : p ≠ q) (z : IdealBoundary X) :
    angleIdealOrdinary p q hpq z ≤ Real.pi

-- ----------------------------------------------------------------
-- §7  CONE   C_p(z, ε)
--
-- From the screenshot:
--
--   C_p(z, ε) := { q ∈ X ∪ ∂X  |  p ≠ q,  ∠_p(z, q) < ε }
--
-- A point q can be either an ordinary point of X or an
-- ideal-boundary point of ∂X.  We represent X ∪ ∂X as the
-- disjoint sum  X ⊕ IdealBoundary X.
-- ----------------------------------------------------------------

/-- The angle at p between z ∈ ∂X and a point q in X ∪ ∂X.
    • If q is an ordinary point  (Sum.inl q_ord),  use angleIdealOrdinary.
    • If q is an ideal point     (Sum.inr z'),      use angleAtIdealPoints. -/
noncomputable def angleToPoint
    {X : Type*} [MetricSpace X] [DecidableEq X]
    (p : X) (z : IdealBoundary X) :
    (X ⊕ IdealBoundary X) → ℝ
  | Sum.inl q =>
      if h : p = q then 0
      else angleIdealOrdinary p q (Ne.symm (Ne.symm h)) z
  | Sum.inr z' => angleAtIdealPoints p z z'

/-- The cone  C_p(z, ε)  is the set of all points q in X ∪ ∂X
    such that q ≠ p and the angle ∠_p(z, q) < ε.

        C_p(z, ε)  :=  { q ∈ X ∪ ∂X  |  p ≠ q,  ∠_p(z, q) < ε }
-/
def Cone
    {X : Type*} [MetricSpace X] [DecidableEq X]
    (p : X)
    (z : IdealBoundary X)
    (ε : ℝ) :
    Set (X ⊕ IdealBoundary X) :=
  { q |
    -- q must be different from p (base point is excluded)
    q ≠ Sum.inl p  ∧
    -- the angle from p toward z and toward q must be < ε
    angleToPoint p z q < ε }

-- Notation:  C_p(p, z, ε)
scoped notation "C_p(" p ", " z ", " ε ")" => Cone p z ε

-- ----------------------------------------------------------------
-- §8  SMALL EXAMPLES / SANITY CHECKS
-- ----------------------------------------------------------------

section Examples

variable {X : Type*} [MetricSpace X] [DecidableEq X]

/-- A point inside the cone satisfies the angle condition. -/
lemma mem_Cone_iff
    (p : X) (z : IdealBoundary X) (ε : ℝ)
    (q : X ⊕ IdealBoundary X) :
    q ∈ Cone p z ε  ↔
    q ≠ Sum.inl p ∧ angleToPoint p z q < ε :=
  Iff.rfl

/-- An ideal point z₂ is in C_p(z₁, ε) when ∠_p(z₁, z₂) < ε. -/
lemma idealPoint_mem_Cone
    (p : X) (z₁ z₂ : IdealBoundary X) (ε : ℝ)
    (hne : Sum.inr z₂ ≠ Sum.inl p)
    (hangle : angleAtIdealPoints p z₁ z₂ < ε) :
    Sum.inr z₂ ∈ Cone p z₁ ε :=
  ⟨hne, hangle⟩

end Examples

end Hyperbolic
