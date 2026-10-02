import BernsteinObstacle.PhysicalSobolevGraph
import BernsteinObstacle.PhysicalH01Recovery
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Sequences

open MeasureTheory Set Function Filter Topology
open scoped ENNReal InnerProductSpace

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Addition of actual smooth compactly supported test functions keeps
their support inside the same open physical domain. -/
def physicalSobolevTestAdd {Ω : Set E} (φ ψ : PhysicalSobolevTest Ω) :
    PhysicalSobolevTest Ω :=
  ⟨φ.1 + ψ.1, φ.2.1.add ψ.2.1, φ.2.2.1.add ψ.2.2.1,
    (tsupport_add φ.1 ψ.1).trans (union_subset φ.2.2.2 ψ.2.2.2)⟩

def physicalSobolevTestSmul {Ω : Set E} (c : ℝ) (φ : PhysicalSobolevTest Ω) :
    PhysicalSobolevTest Ω :=
  ⟨c • φ.1, φ.2.1.const_smul c,
    φ.2.2.1.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_right (fun _ => c) φ.1),
    (tsupport_smul_subset_right (fun _ => c) φ.1).trans φ.2.2.2⟩

/-- The smooth compactly supported part of the actual H1 graph. On an
open domain the represented L2 function uniquely determines its weak partials. -/
def physicalH1SmoothSubmodule (Ω : Set E) (_hΩ : IsOpen Ω) :
    Submodule ℝ (physicalH1Submodule Ω) where
  carrier := {z | ∃ φ : PhysicalSobolevTest Ω, physicalTestLp φ = z.1 0}
  zero_mem' := by
    refine ⟨⟨0, contDiff_const, ?_, ?_⟩, ?_⟩
    · simp [HasCompactSupport]
    · simp
    · exact MemLp.toLp_zero _
  add_mem' := by
    intro z w hz hw
    rcases hz with ⟨φ, hφ⟩
    rcases hw with ⟨ψ, hψ⟩
    refine ⟨physicalSobolevTestAdd φ ψ, ?_⟩
    change physicalTestLp φ + physicalTestLp ψ = z.1 0 + w.1 0
    rw [hφ, hψ]
  smul_mem' := by
    intro c z hz
    rcases hz with ⟨φ, hφ⟩
    refine ⟨physicalSobolevTestSmul c φ, ?_⟩
    change c • physicalTestLp φ = c • z.1 0
    rw [hφ]

/-- The concrete zero-trace Hilbert space is the H1 closure of actual
smooth compactly supported functions. This is the standard closure definition
of H01; it does not assume an unproved boundary trace characterization. -/
def physicalH01Submodule (Ω : Set E) (hΩ : IsOpen Ω) :
    Submodule ℝ (physicalH1Submodule Ω) :=
  (physicalH1SmoothSubmodule Ω hΩ).topologicalClosure

theorem isClosed_physicalH01Submodule (Ω : Set E) (hΩ : IsOpen Ω) :
    IsClosed (physicalH01Submodule Ω hΩ : Set (physicalH1Submodule Ω)) :=
  (physicalH1SmoothSubmodule Ω hΩ).isClosed_topologicalClosure

/-- Completeness follows from the proved concrete H1 graph and the
proved closed subspace, with no assumed Sobolev-space realization. -/
instance physicalH01CompleteSpace (Ω : Set E) (hΩ : IsOpen Ω) :
    CompleteSpace (physicalH01Submodule Ω hΩ) :=
  (isClosed_physicalH01Submodule Ω hΩ).completeSpace_coe

/-- Convergence in the actual H1 Hilbert graph is exactly convergence of
the function and each actual weak partial in their L2 equivalence classes. -/
theorem tendsto_physicalH1_iff_components {Ω : Set E}
    (z : ℕ → physicalH1Submodule Ω) (w : physicalH1Submodule Ω) :
    Tendsto z atTop (𝓝 w) ↔
      ∀ j : Fin (d + 1), Tendsto (fun n => (z n).1 j) atTop (𝓝 (w.1 j)) := by
  rw [tendsto_subtype_rng]
  constructor
  · intro h j
    exact (PiLp.continuous_apply 2 _ j).tendsto w.1 |>.comp h
  · intro h
    have hp := tendsto_pi_nhds.mpr h
    exact (PiLp.continuous_toLp 2 _).tendsto w.1.ofLp |>.comp hp

/-- A smooth test function has its actual classical derivative as its
weak derivative and is embedded in the concrete H1 graph. -/
def physicalTestH1Witness {Ω : Set E} (hΩ : IsOpen Ω) (φ : PhysicalSobolevTest Ω) :
    SobolevH01Port.MemW1pWitness 2 φ.1 Ω := by
  refine ⟨(φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2.1).restrict Ω,
    gradient φ.1, ?_, ?_⟩
  · intro i
    simp_rw [gradient_component_eq_fderiv_apply]
    exact (((φ.2.1.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (φ.2.2.1.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict Ω
  · intro i
    simp_rw [gradient_component_eq_fderiv_apply]
    exact hasWeakPartialDeriv_of_contDiff hΩ (φ.2.1.of_le (by simp))

def physicalH1OfTest {Ω : Set E} (hΩ : IsOpen Ω) (φ : PhysicalSobolevTest Ω) :
    physicalH1Submodule Ω :=
  physicalH1OfWitness (physicalTestH1Witness hΩ φ)

theorem physicalH1OfTest_mem_smooth {Ω : Set E} (hΩ : IsOpen Ω)
    (φ : PhysicalSobolevTest Ω) :
    physicalH1OfTest hΩ φ ∈ physicalH1SmoothSubmodule Ω hΩ :=
  ⟨φ, rfl⟩

theorem physicalH1SmoothSubmodule_eq_range {Ω : Set E} (hΩ : IsOpen Ω) :
    (physicalH1SmoothSubmodule Ω hΩ : Set (physicalH1Submodule Ω)) =
      Set.range (physicalH1OfTest hΩ) := by
  ext z
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, physicalH1_function_injective hΩ ?_⟩
    exact hφ
  · rintro ⟨φ, rfl⟩
    exact physicalH1OfTest_mem_smooth hΩ φ

/-- The test-function embedding has precisely the same convergence
criterion as the existing integral-based H01 approximation data. -/
theorem tendsto_physicalH1OfTest_iff {Ω : Set E} (hΩ : IsOpen Ω)
    (φ : ℕ → PhysicalSobolevTest Ω) {u : E → ℝ}
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω) :
    Tendsto (fun n => physicalH1OfTest hΩ (φ n)) atTop (𝓝 (physicalH1OfWitness hw)) ↔
      Tendsto (fun n => eLpNorm ((φ n).1 - u) 2 (volume.restrict Ω)) atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ (φ n).1 x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        2 (volume.restrict Ω)) atTop (𝓝 0) := by
  have hfun :
      Tendsto (fun n => (physicalH1OfTest hΩ (φ n)).1 0) atTop
          (𝓝 ((physicalH1OfWitness hw).1 0)) ↔
        Tendsto (fun n => eLpNorm ((φ n).1 - u) 2 (volume.restrict Ω)) atTop (𝓝 0) :=
    Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (φ n).1)
      (fun n => (physicalTestH1Witness hΩ (φ n)).memLp) u hw.memLp
  have hgrad (i : Fin d) :
      Tendsto (fun n => (physicalH1OfTest hΩ (φ n)).1 i.succ) atTop
          (𝓝 ((physicalH1OfWitness hw).1 i.succ)) ↔
        Tendsto (fun n => eLpNorm
          (fun x => (fderiv ℝ (φ n).1 x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          2 (volume.restrict Ω)) atTop (𝓝 0) := by
    have h :
        Tendsto (fun n => (physicalH1OfTest hΩ (φ n)).1 i.succ) atTop
            (𝓝 ((physicalH1OfWitness hw).1 i.succ)) ↔
          Tendsto (fun n => eLpNorm
            (fun x => gradient (φ n).1 x i - hw.weakGrad x i)
            2 (volume.restrict Ω)) atTop (𝓝 0) :=
      Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := atTop)
        (fun n x => gradient (φ n).1 x i)
        (fun n => (physicalTestH1Witness hΩ (φ n)).weakGrad_component_memLp i)
        (fun x => hw.weakGrad x i) (hw.weakGrad_component_memLp i)
    simpa only [gradient_component_eq_fderiv_apply] using h
  rw [tendsto_physicalH1_iff_components]
  constructor
  · intro h
    exact ⟨hfun.mp (h 0), fun i => (hgrad i).mp (h i.succ)⟩
  · rintro ⟨hf, hg⟩ j
    exact Fin.cases (hfun.mpr hf) (fun i => (hgrad i).mpr (hg i)) j

variable [NeZero d]

/-- Faithfulness to the project's integral-based H01: membership in the
constructed closed Hilbert subspace is equivalent to actual simultaneous
smooth L2 approximation of the function and its weak partials. -/
theorem physicalH1OfWitness_mem_H01_iff {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω) :
    physicalH1OfWitness hw ∈ physicalH01Submodule Ω hΩ ↔ SobolevH01Port.MemH01 u Ω := by
  constructor
  · intro hz
    change physicalH1OfWitness hw ∈ closure (physicalH1SmoothSubmodule Ω hΩ : Set _) at hz
    rcases mem_closure_iff_seq_limit.mp hz with ⟨z, hz, hconv⟩
    choose φ hφ using hz
    have heq (n : ℕ) : physicalH1OfTest hΩ (φ n) = z n :=
      physicalH1_function_injective hΩ (hφ n)
    have htest := hconv.congr fun n => (heq n).symm
    have herr := (tendsto_physicalH1OfTest_iff hΩ φ hw).mp htest
    exact ⟨hw.memW1p, hw, fun n => (φ n).1, fun n => (φ n).2.1,
      fun n => (φ n).2.2.1, fun n => (φ n).2.2.2, herr.1, herr.2⟩
  · intro hu
    rcases hu.2 with ⟨hw', φ, hφ, hc, hs, hf, hg⟩
    let ψ : ℕ → PhysicalSobolevTest Ω := fun n => ⟨φ n, hφ n, hc n, hs n⟩
    have hconv := (tendsto_physicalH1OfTest_iff hΩ ψ hw').mpr ⟨hf, hg⟩
    rw [physicalH1OfWitness_independent hΩ hw' hw] at hconv
    change physicalH1OfWitness hw ∈ closure (physicalH1SmoothSubmodule Ω hΩ : Set _)
    exact mem_closure_of_tendsto hconv
      (Eventually.of_forall fun n => physicalH1OfTest_mem_smooth hΩ (ψ n))

/-- The canonical actual function and weak-gradient witness of a graph
element, formed from its L2 representatives. -/
def physicalH1Witness {Ω : Set E} (z : physicalH1Submodule Ω) :
    SobolevH01Port.MemW1pWitness 2 (z.1 0) Ω :=
  ⟨Lp.memLp (z.1 0), fun x => WithLp.toLp 2 (fun i => z.1 i.succ x),
    fun i => Lp.memLp (z.1 i.succ), (mem_physicalH1Submodule_iff z.1).mp z.2⟩

omit [NeZero d] in
theorem physicalH1OfWitness_canonical {Ω : Set E} (hΩ : IsOpen Ω)
    (z : physicalH1Submodule Ω) : physicalH1OfWitness (physicalH1Witness z) = z := by
  apply physicalH1_function_injective hΩ
  exact Lp.toLp_coeFn (z.1 0) (Lp.memLp (z.1 0))

/-- Every element of the concrete zero-trace Hilbert subspace represents
an actual H01 function under the existing approximation definition. -/
theorem memH01_of_mem_physicalH01Submodule {Ω : Set E} (hΩ : IsOpen Ω)
    {z : physicalH1Submodule Ω} (hz : z ∈ physicalH01Submodule Ω hΩ) :
    SobolevH01Port.MemH01 (z.1 0) Ω := by
  apply (physicalH1OfWitness_mem_H01_iff hΩ (physicalH1Witness z)).mp
  rw [physicalH1OfWitness_canonical hΩ z]
  exact hz

/-- Embed actual H01 function/gradient data in the constructed Hilbert
space. The membership proof is obtained from the proved faithfulness theorem. -/
def physicalH01OfWitness {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω) (hu : SobolevH01Port.MemH01 u Ω) :
    physicalH01Submodule Ω hΩ :=
  ⟨physicalH1OfWitness hw, (physicalH1OfWitness_mem_H01_iff hΩ hw).mpr hu⟩

theorem physicalH01OfWitness_independent {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw₁ hw₂ : SobolevH01Port.MemW1pWitness 2 u Ω) (hu : SobolevH01Port.MemH01 u Ω) :
    physicalH01OfWitness hΩ hw₁ hu = physicalH01OfWitness hΩ hw₂ hu := by
  apply Subtype.ext
  exact physicalH1OfWitness_independent hΩ hw₁ hw₂

omit [NeZero d] in
theorem physicalH01_norm_sq {Ω : Set E} (hΩ : IsOpen Ω)
    (z : physicalH01Submodule Ω hΩ) :
    ‖z‖ ^ 2 = ‖z.1.1 0‖ ^ 2 + ∑ i : Fin d, ‖z.1.1 i.succ‖ ^ 2 :=
  physicalH1_norm_sq z.1

/-- Actual conforming physical recovery, with proved interior-supported
H01 approximation, represented in one concrete zero-trace Hilbert space. -/
def physicalMeshH01Element {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0)
    {Ω : Set E} (hΩ : IsOpen Ω) (hs : tsupport (physicalMeshRecovery b n hn f) ⊆ Ω) :
    physicalH01Submodule Ω hΩ :=
  physicalH01OfWitness hΩ (physicalMeshH1Witness b hb hboundary n hn f hf hΩ)
    (memH01_physicalMeshRecovery b hb hboundary n hn f hf hΩ hs)

end

end BernsteinObstacle
