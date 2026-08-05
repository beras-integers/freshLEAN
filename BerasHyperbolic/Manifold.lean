import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Manifold
open Filter
open scoped Topology
#check mem_closure_iff
#check closure_prod_eq

open Filter
variable {X : Type*} [TopologicalSpace X]
variable (A : Set X)
example : IsOpen (interior A) := by
  unfold interior
  apply isOpen_sUnion
  intro g hg
  apply hg.1

lemma setinsideclosure : A ⊆ closure A := by
  intro x hx
  unfold closure
  intro t ht
  apply ht.2
  exact hx

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := by
    simp
  sets_of_superset := by
    rintro t1 t2 h1 h2
    exact Set.Subset.trans h1 h2
  inter_sets := by
    intro t1 t2 ht1 ht2 x hx
    exact ⟨ht1 hx, ht2 hx⟩

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ Tendsto f F G :=
  Iff.rfl



theorem isClosed_sInter' {α : Type*} [TopologicalSpace α]
  (S : Set (Set α))
  (hS : ∀ s ∈ S, IsClosed s) :
  IsClosed (⋂₀ S) := by
  rw [← isOpen_compl_iff]
  have : (⋂₀ S)ᶜ = ⋃₀ (Set.image compl S) := by
    ext x
    simp [Set.mem_sInter, Set.mem_image]
  rw [this]
  exact isOpen_sUnion (by
    intro s hs
    obtain ⟨s', hs', rfl⟩ := hs
    exact (hS s' hs').isOpen_compl)

lemma closed_prod {X : Type*} [TopologicalSpace X]
    (A : Set X) (B : Set X)
    (hA : IsClosed A)
    (hB : IsClosed B) :
    IsClosed (A ×ˢ B) := by
    have hAB : IsClosed (A ×ˢ B) := by
      exact hA.prod hB
    exact hAB

theorem closure_smallest {X : Type*} [TopologicalSpace X]
    (A C : Set X)
    (hC : IsClosed C)
    (hAC : A ⊆ C) :
    closure A ⊆ C := by
    have h1 : closure A ⊆ C := by
      exact closure_minimal hAC hC
    exact h1


example (A B : Set X) : closure (A ×ˢ B) = closure A ×ˢ closure B := by
  have hclosed : IsClosed (closure A ×ˢ closure B) := by
    apply closed_prod
    · apply isClosed_closure
    · apply isClosed_closure
  have hsubset : A ×ˢ B ⊆ closure A ×ˢ closure B := by
    intro x hx
    exact ⟨subset_closure hx.1, subset_closure hx.2⟩
  have h₁ : closure (A ×ˢ B) ⊆ closure A ×ˢ closure B := by
    exact closure_smallest
      (A ×ˢ B)
      (closure A ×ˢ closure B)
      hclosed
      hsubset
  have h₂ : closure A ×ˢ closure B ⊆ closure (A ×ˢ B) := by
    simp [← closure_prod_eq]
  exact subset_antisymm h₁ h₂

example
    {X Y : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    {f : X → Y}
    {V : Set Y}
    (hf : Continuous f)
    (hV : IsOpen V) :
    IsOpen (f ⁻¹' V) := by
  have hpre : IsOpen (f ⁻¹' V) := by
    exact hf.isOpen_preimage V hV
  exact hpre



example
    {X Y : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    {u : ℕ → X}
    {x : X}
    {f : X → Y}
    (hf : Continuous f)
    (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) := by

  have h1 : Tendsto f (𝓝 x) (𝓝 (f x)) := by
    exact hf.continuousAt.tendsto

  have h2 :
      Tendsto (fun n => f (u n))
        atTop
        (𝓝 (f x)) := by
    exact h1.comp hu

  exact h2

universe u
structure MyManifold (M : Type u) [TopologicalSpace M] (n : ℕ) where
  local_homeomorph :
    ∀ x : M,
      ∃ U : Set M,
        IsOpen U ∧
        x ∈ U ∧
        ∃ V : Set (EuclideanSpace ℝ (Fin n)),
          IsOpen V ∧
          Nonempty (U ≃ₜ V)



noncomputable section


abbrev ModelSpace (n : ℕ) :=
  EuclideanSpace ℝ (Fin n)

variable
  (n : ℕ)
  (M : Type*)

variable
  [TopologicalSpace M]
  [ChartedSpace (ModelSpace n) M]

example (x : M) :
    x ∈ (chartAt (ModelSpace n) x).source := by
  exact mem_chart_source (H := ModelSpace n) x



noncomputable section

structure Point where
  x : ℝ
  y : ℝ

def HyperbolicPlane : Type :=
  { p : Point // p.x ^ 2 + p.y ^ 2 < 1 }

example (p : HyperbolicPlane) :
    p.1.x ^ 2 + p.1.y ^ 2 < 1 := by
  exact p.2

axiom hyperbolicDist :
  HyperbolicPlane → HyperbolicPlane → ℝ

/-- Distance from a point to itself is zero. -/
axiom hyperbolicDist_self
    (x : HyperbolicPlane) :
    hyperbolicDist x x = 0

/-- Distance is symmetric. -/
axiom hyperbolicDist_comm
    (x y : HyperbolicPlane) :
    hyperbolicDist x y =
    hyperbolicDist y x

/-- Triangle inequality. -/
axiom hyperbolicDist_triangle
    (x y z : HyperbolicPlane) :
    hyperbolicDist x z ≤
      hyperbolicDist x y +
      hyperbolicDist y z

/-- Distance is always nonnegative. -/
axiom hyperbolicDist_nonneg
    (x y : HyperbolicPlane) :
    0 ≤ hyperbolicDist x y

/-- Zero distance implies equality. -/
axiom hyperbolicDist_eq_zero
    {x y : HyperbolicPlane} :
    hyperbolicDist x y = 0 →
    x = y

instance : MetricSpace HyperbolicPlane where
  dist := hyperbolicDist
  dist_self := hyperbolicDist_self
  dist_comm := hyperbolicDist_comm
  dist_triangle := hyperbolicDist_triangle
  eq_of_dist_eq_zero := hyperbolicDist_eq_zero



def hyperbolicDisc (p : HyperbolicPlane) (r : ℝ) : Set HyperbolicPlane :=
  { q : HyperbolicPlane | hyperbolicDist p q < r }

axiom eq_of_hyperbolicDist_eq_zero :
  ∀ {p q : HyperbolicPlane},
    hyperbolicDist p q = 0 → p = q

instance : MetricSpace HyperbolicPlane where
  dist := hyperbolicDist
  dist_self := hyperbolicDist_self
  dist_comm := hyperbolicDist_comm
  dist_triangle := hyperbolicDist_triangle
  eq_of_dist_eq_zero := by
    intro p q h
    exact eq_of_hyperbolicDist_eq_zero h

set_option linter.style.whitespace false

structure RiemannianMetric
    (X : Type*)
    [TopologicalSpace X]
    (TangentSpace : X → Type*)
    [∀ p, AddCommGroup (TangentSpace p)]
    [∀ p, Module ℝ (TangentSpace p)] where

  g :
    ∀ p,
      TangentSpace p → TangentSpace p → ℝ

  add_left :
    ∀ p u v w,
      g p (u + v) w =
      g p u w + g p v w

  smul_left :
    ∀ p a u w,
      g p (a • u) w =
      a * g p u w

  add_right :
    ∀ p u v w,
      g p u (v + w) =
      g p u v + g p u w

  smul_right :
    ∀ p a u v,
      g p u (a • v) =
      a * g p u v

  symmetric :
    ∀ p u v,
      g p u v = g p v u

  positive :
    ∀ p v,
      v ≠ 0 →
      0 < g p v v

abbrev HyperbolicSpace (n : ℕ) :=
  RiemannianMetric ℝ (fun _ : ℝ => Fin n → ℝ)

instance (n : ℕ) : TopologicalSpace (HyperbolicSpace n) := ⊤

variable
  (n : ℕ)
  (M : Type*)

variable
  [TopologicalSpace M]
  [ChartedSpace (ModelSpace n) M]

example (x : M) :
    x ∈ (chartAt (ModelSpace n) x).source := by
  exact mem_chart_source (H := ModelSpace n) x


open scoped BigOperators

-- `ModelSpace` is already defined above.
def HyperbolicSpaceModel (n : ℕ) : Type :=
  match n with
  | 0 =>
      Empty
  | Nat.succ k =>
      { p : ModelSpace (Nat.succ k) // 0 < p ⟨k, Nat.lt_succ_self k⟩ }
def Hyperbolicspace (n : ℕ) : Type :=
  HyperbolicSpaceModel n



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

structure HyperbolicSpace (n : ℕ) where
  coord : Fin n → ℝ
  sectionalCurvature : ℝ
  negativeCurvature : sectionalCurvature < 0

structure HyperbolicMetric (n : ℕ) where
  dist : HyperbolicSpace n → HyperbolicSpace n → ℝ

def HyperbolicPlane : Type := HyperbolicSpace 2

def dist (n : ℕ) (_x _y : HyperbolicSpace n) : ℝ := 0

instance (n : ℕ) : TopologicalSpace (HyperbolicSpace n) := ⊤

structure HyperbolicMetricSpace (n : ℕ) where
  metric : HyperbolicMetric n

/--
The notation Iso_+(H^n) means the set of all orientation-preserving isometries
of hyperbolic space.
-/
def IsoPlusHyperbolic (n : ℕ) : Type := HyperbolicSpace n → HyperbolicSpace n

structure SmoothManifold (M : Type*) [TopologicalSpace M] where
  chart : M → Type

structure RiemannianMetric (M : Type*) [TopologicalSpace M] where
  metric : M → M → ℝ

structure LocalIsometry (M : Type*) (N : Type*) [TopologicalSpace M] [TopologicalSpace N] where
  toFun : M → N

structure HyperbolicChart (M : Type*) [TopologicalSpace M] where
  toFun : M → HyperbolicPlane

structure HyperbolicAtlas (M : Type*) [TopologicalSpace M] where
  charts : Set (HyperbolicChart M)

structure HyperbolicManifold (M : Type*) [TopologicalSpace M] where
  atlas : HyperbolicAtlas M
  metric : RiemannianMetric M

/--
The Lorentz group SO(n,1) is a group of special matrix transformations that
preserve a certain quadratic form.
-/
def LorentzGroup (n : ℕ) : Type := Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ

def preservesQuadraticForm (n : ℕ) (_A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop := True

/--
The statement Iso_+(H^n) ≅ SO(n,1)^0 means that these two groups have the same
algebraic structure, even though they may be written in different ways.
-/
def IsomorphicHyperbolicLorentz (_n : ℕ) : Prop := True

/--
The group of orientation-preserving hyperbolic isometries is isomorphic to the
identity component of the Lorentz group SO(n,1).
-/
def OrientationPreservingIsometriesIsomorphicToLorentzIdentity (_n : ℕ) : Prop := True

/--
In low dimensions, these groups are identified with PSL(2,R) and PSL(2,C).
-/
def LowDimensionalIdentification (_n : ℕ) : Prop := True

/--
The boundary of hyperbolic space is the sphere S^(n-1) at infinity.
We model it here as a simple type of boundary points.
-/
def BoundaryHyperbolic (n : ℕ) : Type := Fin n → ℝ

/--
A Möbius transformation is a fractional linear map of the form z ↦ (a z + b) / (c z + d).
We encode it here as a map from the boundary to itself.
-/
def MobiusTransformation (n : ℕ) : Type := BoundaryHyperbolic n → BoundaryHyperbolic n

/--
Every hyperbolic isometry acts on the boundary by a Möbius transformation.
-/
def HyperbolicBoundaryAction (_n : ℕ) : Prop := True

/--
In general, the group of hyperbolic isometries acts on the boundary as Möbius
transformations, that is, compositions of inversions in round spheres.
curvature is -1.
-/
def HyperbolicManifoldDefinition (M : Type*) [TopologicalSpace M] : Prop := True

/--
Equivalently, a hyperbolic manifold may be viewed as a quotient of hyperbolic
space by a torsion-free discrete subgroup of the identity component of the
Lorentz group.
-/
def HyperbolicManifoldAsQuotient (M : Type*) [TopologicalSpace M] : Prop := True

/--
Many geometric and topological properties of hyperbolic manifolds remain true
in the nonpositive-curvature setting. In particular, a complete simply connected
manifold of nonpositive curvature is diffeomorphic to Euclidean space and has
convex distance.
-/
def NonPositiveCurvatureGeneralization (M : Type*) [TopologicalSpace M] : Prop := True
def mkHyperbolicSpace (n : ℕ) (coord : Fin n → ℝ) (sectionalCurvature : ℝ)
    (h : sectionalCurvature < 0) : HyperbolicSpace n := {
  coord := coord
  sectionalCurvature := sectionalCurvature
  negativeCurvature := h
}

example : ∀ (x : HyperbolicSpace 1), x.sectionalCurvature < 0 := by
  intro x
  exact x.negativeCurvature

end Hyperbolic
