import BernsteinObstacle.PhysicalWeakLimits
import BernsteinObstacle.PhysicalGlobalSobolev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual

open MeasureTheory Set Function Filter Topology
open scoped ENNReal InnerProductSpace

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual smooth compactly supported scalar test functions in Ω. -/
def PhysicalSobolevTest (Ω : Set E) :=
  {φ : E → ℝ // ContDiff ℝ (⊤ : ENat) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω}

/-- Hilbert product of actual L2 equivalence classes: coordinate zero is
the function and the remaining coordinates are its weak partials. -/
abbrev PhysicalH1Ambient (Ω : Set E) :=
  PiLp 2 (fun _ : Fin (d + 1) => Lp ℝ 2 (volume.restrict Ω))

def physicalTestLp {Ω : Set E} (φ : PhysicalSobolevTest Ω) : Lp ℝ 2 (volume.restrict Ω) :=
  ((φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2.1).restrict Ω).toLp φ.1

def physicalTestDerivativeLp {Ω : Set E} (φ : PhysicalSobolevTest Ω) (i : Fin d) :
    Lp ℝ 2 (volume.restrict Ω) := by
  let Dφ : E → ℝ := fun x => (fderiv ℝ φ.1 x) (EuclideanSpace.single i 1)
  have hD : Continuous Dφ := (φ.2.1.continuous_fderiv (by simp)).clm_apply continuous_const
  exact ((hD.memLp_of_hasCompactSupport
    (φ.2.2.1.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict Ω).toLp Dφ

/-- Each integration-by-parts condition is the kernel of a genuine
continuous linear functional on the actual L2 Hilbert product. -/
def physicalWeakForm {Ω : Set E} (φ : PhysicalSobolevTest Ω) (i : Fin d) :
    PhysicalH1Ambient Ω →L[ℝ] ℝ :=
  (innerSL ℝ (physicalTestDerivativeLp φ i)).comp (PiLp.proj 2 _ 0) +
    (innerSL ℝ (physicalTestLp φ)).comp (PiLp.proj 2 _ i.succ)

theorem integral_mul_Lp_eq_inner {Ω : Set E} (u : Lp ℝ 2 (volume.restrict Ω))
    {φ : E → ℝ} (hφ : MemLp φ 2 (volume.restrict Ω)) :
    (∫ x in Ω, u x * φ x) = ⟪u, hφ.toLp φ⟫_ℝ := by
  simpa only [Lp.toLp_coeFn] using integral_mul_eq_L2_inner (Lp.memLp u) hφ

theorem physicalWeakForm_eq_integrals {Ω : Set E} (φ : PhysicalSobolevTest Ω)
    (i : Fin d) (z : PhysicalH1Ambient Ω) :
    physicalWeakForm φ i z =
      (∫ x in Ω, z 0 x * (fderiv ℝ φ.1 x) (EuclideanSpace.single i 1)) +
      (∫ x in Ω, z i.succ x * φ.1 x) := by
  change ⟪physicalTestDerivativeLp φ i, z 0⟫_ℝ + ⟪physicalTestLp φ, z i.succ⟫_ℝ = _
  congr 1
  · have hDmem : MemLp (fun x => (fderiv ℝ φ.1 x) (EuclideanSpace.single i 1))
        2 (volume.restrict Ω) :=
      (((φ.2.1.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (φ.2.2.1.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict Ω
    exact (real_inner_comm (z 0) (physicalTestDerivativeLp φ i)).trans
      (integral_mul_Lp_eq_inner (z 0) hDmem).symm
  · exact (real_inner_comm (z i.succ) (physicalTestLp φ)).trans
      (integral_mul_Lp_eq_inner (z i.succ) _).symm

/-- The actual weak-derivative graph, rather than an abstract Sobolev-space
parameter. Membership is subsequently proved equivalent to integral weak
partial derivatives of the represented function. -/
def physicalH1Submodule (Ω : Set E) : Submodule ℝ (PhysicalH1Ambient Ω) :=
  ⨅ (i : Fin d) (φ : PhysicalSobolevTest Ω), (physicalWeakForm φ i).ker

theorem mem_physicalH1Submodule_iff {Ω : Set E} (z : PhysicalH1Ambient Ω) :
    z ∈ physicalH1Submodule Ω ↔
      ∀ i : Fin d, SobolevH01Port.HasWeakPartialDeriv i (fun x => z i.succ x) (z 0) Ω := by
  simp only [physicalH1Submodule, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hz i φ hφ hc hs
    have h := hz i ⟨φ, hφ, hc, hs⟩
    change physicalWeakForm ⟨φ, hφ, hc, hs⟩ i z = 0 at h
    have hzero :=
      (physicalWeakForm_eq_integrals (⟨φ, hφ, hc, hs⟩ : PhysicalSobolevTest Ω) i z).symm.trans h
    exact eq_neg_of_add_eq_zero_left hzero
  · intro hz i φ
    change physicalWeakForm φ i z = 0
    rw [physicalWeakForm_eq_integrals]
    exact add_eq_zero_iff_eq_neg.mpr (hz i φ.1 φ.2.1 φ.2.2.1 φ.2.2.2)

theorem isClosed_physicalH1Submodule (Ω : Set E) :
    IsClosed (physicalH1Submodule Ω : Set (PhysicalH1Ambient Ω)) := by
  simp only [physicalH1Submodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun φ => (physicalWeakForm φ i).isClosed_ker

instance physicalH1CompleteSpace (Ω : Set E) : CompleteSpace (physicalH1Submodule Ω) :=
  (isClosed_physicalH1Submodule Ω).completeSpace_coe

/-- The inherited Hilbert norm is precisely the sum of the squared L2
function norm and the squared L2 norms of all weak partials. -/
theorem physicalH1_norm_sq {Ω : Set E} (z : physicalH1Submodule Ω) :
    ‖z‖ ^ 2 = ‖z.1 0‖ ^ 2 + ∑ i : Fin d, ‖z.1 i.succ‖ ^ 2 := by
  change ‖(z.1 : PhysicalH1Ambient Ω)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]

/-- On an open set the represented L2 function determines the entire
graph element, because its actual weak partials are unique almost everywhere. -/
theorem physicalH1_function_injective {Ω : Set E} (hΩ : IsOpen Ω) :
    Function.Injective (fun z : physicalH1Submodule Ω => z.1 0) := by
  intro z w h
  change z.1 0 = w.1 0 at h
  apply Subtype.ext
  apply (WithLp.ext_iff 2).mpr
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact h
  · apply Lp.ext
    have hz := (mem_physicalH1Submodule_iff z.1).mp z.2 i
    have hw := (mem_physicalH1Submodule_iff w.1).mp w.2 i
    rw [← h] at hw
    exact ae_eq_of_hasWeakPartialDeriv hΩ hz hw
      ((Lp.memLp (z.1 i.succ)).locallyIntegrable (by norm_num))
      ((Lp.memLp (w.1 i.succ)).locallyIntegrable (by norm_num))

/-- Every point of the concrete closed Hilbert graph represents an actual
integral-based H1 function on Ω. -/
theorem memH1_of_mem_physicalH1Submodule {Ω : Set E} {z : PhysicalH1Ambient Ω}
    (hz : z ∈ physicalH1Submodule Ω) : SobolevH01Port.MemH1 (z 0) Ω := by
  refine ⟨Lp.memLp (z 0), ?_⟩
  intro i
  exact ⟨fun x => z i.succ x, Lp.memLp (z i.succ), (mem_physicalH1Submodule_iff z).mp hz i⟩

/-- Embed an actual function and proved weak-gradient witness into actual
L2 equivalence classes, using no separately postulated Hilbert realization. -/
def physicalH1AmbientOfWitness {Ω : Set E} {u : E → ℝ}
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω) : PhysicalH1Ambient Ω :=
  WithLp.toLp 2 (fun j => Fin.cases (hw.memLp.toLp u)
    (fun i => (hw.weakGrad_component_memLp i).toLp (fun x => hw.weakGrad x i)) j)

theorem physicalH1AmbientOfWitness_mem {Ω : Set E} {u : E → ℝ}
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω) :
    physicalH1AmbientOfWitness hw ∈ physicalH1Submodule Ω := by
  apply (mem_physicalH1Submodule_iff _).mpr
  intro i
  exact hasWeakPartialDeriv_congr_ae (hw.isWeakGrad i)
    hw.memLp.coeFn_toLp (hw.weakGrad_component_memLp i).coeFn_toLp

/-- Actual weak-gradient witness represented in the concrete Hilbert space. -/
def physicalH1OfWitness {Ω : Set E} {u : E → ℝ}
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω) : physicalH1Submodule Ω :=
  ⟨physicalH1AmbientOfWitness hw, physicalH1AmbientOfWitness_mem hw⟩

/-- Different valid choices of actual weak-gradient witness give exactly
the same physical H1 element on an open set. -/
theorem physicalH1OfWitness_independent {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw₁ hw₂ : SobolevH01Port.MemW1pWitness 2 u Ω) :
    physicalH1OfWitness hw₁ = physicalH1OfWitness hw₂ := by
  apply physicalH1_function_injective hΩ
  change hw₁.memLp.toLp u = hw₂.memLp.toLp u
  rfl

/-- The assembled physical recovery is now an element of the concrete H1
Hilbert graph. The H01 closed-subspace and moving-cone bridges remain separate. -/
def physicalMeshH1Element {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0)
    {Ω : Set E} (hΩ : IsOpen Ω) : physicalH1Submodule Ω :=
  physicalH1OfWitness (physicalMeshH1Witness b hb hboundary n hn f hf hΩ)

end

end BernsteinObstacle
