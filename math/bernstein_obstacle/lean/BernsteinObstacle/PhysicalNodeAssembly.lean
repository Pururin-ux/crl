import BernsteinObstacle.PhysicalBoundaryH01
import BernsteinObstacle.PhysicalDiscreteCone
import BernsteinObstacle.AssembledObstacle

open MeasureTheory Set Function Filter Topology

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Physical locations label Bernstein coefficients. These are coefficient
labels, not nodal evaluation values of the resulting Bernstein polynomial. -/
def physicalBernsteinNodeSet {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) : Set E :=
  Set.range (fun z : ι × MultiIndex d n =>
    physicalSimplexPoint (b z.1) (simplexLatticePoint d n hn z.2))

/-- Shared physical coefficient labels identify coincident local labels. -/
def PhysicalBernsteinNode {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) : Type :=
  physicalBernsteinNodeSet b n hn

instance finite_physicalBernsteinNode {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) :
    Finite (PhysicalBernsteinNode b n hn) :=
  (Set.finite_range _).to_subtype

instance fintype_physicalBernsteinNode {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) :
    Fintype (PhysicalBernsteinNode b n hn) := Fintype.ofFinite _

def physicalLocalBernsteinNode {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (T : ι) (α : MultiIndex d n) : PhysicalBernsteinNode b n hn :=
  ⟨physicalSimplexPoint (b T) (simplexLatticePoint d n hn α), ⟨(T, α), rfl⟩⟩

/-- A concrete instance of the upstream assembly interface, with finite
shared physical labels and exactly the labels on the physical boundary. -/
def physicalNodeBernsteinAssembly {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n) :
    BernsteinAssembly ι (PhysicalBernsteinNode b n hn) d n where
  localDof := physicalLocalBernsteinNode b n hn
  boundaryDof := {q | q.1 ∈ frontier (physicalMeshSet b)}

/-- Extend coefficient data solely to feed the existing sampler. No
continuity of this artificial coefficient-data extension is required. -/
def physicalNodeCoefficientExtension {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (c : PhysicalBernsteinNode b n hn → ℝ) (x : E) : ℝ := by
  classical
  exact if hx : x ∈ physicalBernsteinNodeSet b n hn then c ⟨x, hx⟩ else 0

theorem physicalNodeCoefficientExtension_at_localNode {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (c : PhysicalBernsteinNode b n hn → ℝ) (T : ι) (α : MultiIndex d n) :
    physicalNodeCoefficientExtension b n hn c
      (physicalSimplexPoint (b T) (simplexLatticePoint d n hn α)) =
        c (physicalLocalBernsteinNode b n hn T α) := by
  classical
  have hx : physicalSimplexPoint (b T) (simplexLatticePoint d n hn α) ∈
      physicalBernsteinNodeSet b n hn := ⟨(T, α), rfl⟩
  simp only [physicalNodeCoefficientExtension, dif_pos hx, physicalLocalBernsteinNode]

theorem physicalNodeCoefficientExtension_zero_frontier {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (hn : 0 < n)
    (c : PhysicalBernsteinNode b n hn → ℝ)
    (hc : ∀ q ∈ (physicalNodeBernsteinAssembly b n hn).boundaryDof, c q = 0) :
    ∀ x ∈ frontier (physicalMeshSet b), physicalNodeCoefficientExtension b n hn c x = 0 := by
  classical
  intro x hx
  unfold physicalNodeCoefficientExtension
  split_ifs with hnode
  · exact hc ⟨x, hnode⟩ hx
  · rfl

/-- The sampler of arbitrary shared coefficient data equals the intended
local Bernstein polynomial on every closed cell, including its faces. -/
theorem physicalNodeRecovery_eq_on_element {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (n : ℕ) (hn : 0 < n) (c : PhysicalBernsteinNode b n hn → ℝ)
    (T : ι) {x : E} (hx : x ∈ Set.range (physicalSimplexPoint (b T))) :
    physicalMeshRecovery b n hn (physicalNodeCoefficientExtension b n hn c) x =
      physicalBernsteinField (b T) n (fun α => c (physicalLocalBernsteinNode b n hn T α)) x := by
  rw [physicalMeshRecovery_eq_on_element b hb n hn _ T x hx]
  unfold affineBasisPhysicalSamplingRecovery affinePhysicalSamplingRecovery physicalBernsteinField
  congr 1
  funext α
  exact physicalNodeCoefficientExtension_at_localNode b n hn c T α

/-- Zero boundary coefficients give a genuine H01 function, not just
algebraic feasibility or a separately supplied trace witness. -/
theorem memH01_physicalNodeRecovery {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n)
    (c : PhysicalBernsteinNode b n hn → ℝ)
    (hc : ∀ q ∈ (physicalNodeBernsteinAssembly b n hn).boundaryDof, c q = 0) :
    SobolevH01Port.MemH01 (physicalMeshRecovery b n hn (physicalNodeCoefficientExtension b n hn c))
      (interior (physicalMeshSet b)) :=
  memH01_physicalMeshRecovery_on_interior b hb hboundary n hn _
    (physicalNodeCoefficientExtension_zero_frontier b n hn c hc)

def physicalNodeH01Element {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n)
    (c : PhysicalBernsteinNode b n hn → ℝ)
    (hc : ∀ q ∈ (physicalNodeBernsteinAssembly b n hn).boundaryDof, c q = 0) :
    physicalH01Submodule (interior (physicalMeshSet b)) isOpen_interior :=
  physicalH01OfWitness isOpen_interior
    (physicalMeshH1Witness b hb hboundary n hn _
      (physicalNodeCoefficientExtension_zero_frontier b n hn c hc) isOpen_interior)
    (memH01_physicalNodeRecovery b hb hboundary n hn c hc)

/-- Forward bridge from the upstream finite assembled feasible set to the
actual physical H01 coefficient cone. Surjectivity from arbitrary a.e.
intrinsic cone representatives and a conventional mesh-family construction
are separate obligations, not conclusions of this theorem. -/
theorem physicalNodeH01Element_mem_coefficientCone {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n)
    (c : PhysicalBernsteinNode b n hn → ℝ)
    (hc : c ∈ assemblyFeasibleSet (physicalNodeBernsteinAssembly b n hn)) :
    physicalNodeH01Element b hb hboundary n hn c hc.2 ∈
      physicalBernsteinH01Cone b n (interior (physicalMeshSet b)) isOpen_interior := by
  refine ⟨fun T α => c (physicalLocalBernsteinNode b n hn T α), ?_, ?_⟩
  · intro T α
    exact hc.1 _
  · intro T
    let f := physicalNodeCoefficientExtension b n hn c
    let hw : SobolevH01Port.MemW1pWitness 2 (physicalMeshRecovery b n hn f)
        (interior (physicalMeshSet b)) := physicalMeshH1Witness b hb hboundary n hn f
      (physicalNodeCoefficientExtension_zero_frontier b n hn c hc.2) isOpen_interior
    change ∀ᵐ x ∂volume.restrict (interior (physicalMeshSet b)),
      x ∈ Set.range (physicalSimplexPoint (b T)) →
        hw.memLp.toLp (physicalMeshRecovery b n hn f) x =
          physicalBernsteinField (b T) n (fun α => c (physicalLocalBernsteinNode b n hn T α)) x
    filter_upwards [hw.memLp.coeFn_toLp] with x hx hxT
    rw [hx]
    exact physicalNodeRecovery_eq_on_element b hb n hn c T hxT

end

end BernsteinObstacle
