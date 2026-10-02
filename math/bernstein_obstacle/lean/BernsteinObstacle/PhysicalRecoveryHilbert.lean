import BernsteinObstacle.PhysicalSobolevCone
import BernsteinObstacle.PhysicalGlobalError

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-- A C1 compactly supported function has a bounded derivative and hence
is globally Lipschitz. Proving this generically keeps the continuous-linear-map
instances explicit when it is later applied to a physical Frechet derivative. -/
theorem exists_lipschitzWith_of_contDiff_compact {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ M : ℝ≥0, LipschitzWith M f := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hcont
  let M : ℝ≥0 := ⟨max B 0, le_max_right B 0⟩
  refine ⟨M, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (hf.differentiable one_ne_zero)
  intro x
  exact_mod_cast (hB x).trans (le_max_left B 0)

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Joint actual L2 errors are exactly strong convergence of the actual
H1 function/weak-gradient classes. -/
theorem tendsto_physicalH1OfWitness_iff {Ω : Set E} {u : ℕ → E → ℝ} {f : E → ℝ}
    (hw : ∀ n, SobolevH01Port.MemW1pWitness 2 (u n) Ω)
    (hf : SobolevH01Port.MemW1pWitness 2 f Ω) :
    Tendsto (fun n => physicalH1OfWitness (hw n)) atTop (𝓝 (physicalH1OfWitness hf)) ↔
      Tendsto (fun n => eLpNorm (u n - f) 2 (volume.restrict Ω)) atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto (fun n => eLpNorm
        (fun x => (hw n).weakGrad x i - hf.weakGrad x i)
        2 (volume.restrict Ω)) atTop (𝓝 0) := by
  have hfun := Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := atTop)
    u (fun n => (hw n).memLp) f hf.memLp
  have hgrad (i : Fin d) := Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := atTop)
    (fun n x => (hw n).weakGrad x i) (fun n => (hw n).weakGrad_component_memLp i)
    (fun x => hf.weakGrad x i) (hf.weakGrad_component_memLp i)
  rw [tendsto_physicalH1_iff_components]
  constructor
  · intro h
    exact ⟨hfun.mp (h 0), fun i => (hgrad i).mp (h i.succ)⟩
  · rintro ⟨hf, hg⟩ j
    exact Fin.cases (hfun.mpr hf) (fun i => (hgrad i).mpr (hg i)) j

variable [NeZero d]

theorem tendsto_physicalH01OfWitness_iff {Ω : Set E} (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ} {f : E → ℝ}
    (hw : ∀ n, SobolevH01Port.MemW1pWitness 2 (u n) Ω)
    (hf : SobolevH01Port.MemW1pWitness 2 f Ω)
    (hu : ∀ n, SobolevH01Port.MemH01 (u n) Ω) (hff : SobolevH01Port.MemH01 f Ω) :
    Tendsto (fun n => physicalH01OfWitness hΩ (hw n) (hu n)) atTop
        (𝓝 (physicalH01OfWitness hΩ hf hff)) ↔
      Tendsto (fun n => eLpNorm (u n - f) 2 (volume.restrict Ω)) atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto (fun n => eLpNorm
        (fun x => (hw n).weakGrad x i - hf.weakGrad x i)
        2 (volume.restrict Ω)) atTop (𝓝 0) := by
  rw [tendsto_subtype_rng]
  exact tendsto_physicalH1OfWitness_iff hw hf

omit [NeZero d] in
/-- A vector L2 gradient error controls each coordinate error with
constant one in the actual Euclidean norm. -/
theorem tendsto_eLpNorm_component_of_vector {Ω : Set E}
    {G : ℕ → E → E} {g : E → E}
    (h : Tendsto (fun n => eLpNorm (G n - g) 2 (volume.restrict Ω)) atTop (𝓝 0))
    (i : Fin d) :
    Tendsto (fun n => eLpNorm (fun x => G n x i - g x i)
      2 (volume.restrict Ω)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    h (fun _ => bot_le)
  intro n
  exact eLpNorm_mono fun x => PiLp.norm_apply_le (G n x - g x) i

omit [NeZero d] in
theorem tendsto_eLpNorm_restrict_of_subset {F : Type*} [NormedAddCommGroup F]
    {Ω S : Set E} (hs : Ω ⊆ S) {u : ℕ → E → F}
    (h : Tendsto (fun n => eLpNorm (u n) 2 (volume.restrict S)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    h (fun _ => bot_le)
  intro n
  exact eLpNorm_mono_measure (u n) (volume.restrict_mono_set hs)

omit [NeZero d] in
/-- Smooth compact support supplies a global Lipschitz derivative bound
via the bounded continuous second derivative and the mean-value theorem.
Thus the smooth recovery theorem does not assume a separate C1,1 witness. -/
theorem exists_lipschitzWith_fderiv_physicalTest {Ω : Set E} (φ : PhysicalSobolevTest Ω) :
    ∃ M : ℝ≥0, LipschitzWith M (fderiv ℝ φ.1) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ φ.1) := φ.2.1.fderiv_right (m := 1) (by norm_cast)
  exact exists_lipschitzWith_of_contDiff_compact hD (φ.2.2.1.fderiv (𝕜 := ℝ))

theorem physicalTest_memH01 {Ω : Set E} (hΩ : IsOpen Ω) (φ : PhysicalSobolevTest Ω) :
    SobolevH01Port.MemH01 φ.1 Ω := by
  apply (physicalH1OfWitness_mem_H01_iff hΩ (physicalTestH1Witness hΩ φ)).mp
  exact (physicalH1SmoothSubmodule Ω hΩ).le_topologicalClosure
    (physicalH1OfTest_mem_smooth hΩ φ)

def physicalH01OfTest {Ω : Set E} (hΩ : IsOpen Ω) (φ : PhysicalSobolevTest Ω) :
    physicalH01Submodule Ω hΩ :=
  physicalH01OfWitness hΩ (physicalTestH1Witness hΩ φ) (physicalTest_memH01 hΩ φ)

/-- Actual assembled Bernstein recovery of every fixed smooth interior
test function converges strongly in one concrete H1 Hilbert space. Element
sizes may vary; only a uniform local shape bound and maximum-size decay enter. -/
theorem tendsto_physicalMeshH1Element
    {κ : ℕ → Type*} [∀ m, Finite (κ m)]
    (b : ∀ m, κ m → AffineBasis (Fin (d + 1)) ℝ E)
    (hb : ∀ m, physicalFacesMatch (b m)) (hboundary : ∀ m, physicalBoundaryFaces (b m))
    (S : Set E) (hsets : ∀ m, physicalMeshSet (b m) = S)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ interior S)
    (n : ℕ) (hn : 0 < n) (φ : PhysicalSobolevTest Ω)
    (C : ℝ) (hC : 0 ≤ C) (H : ℕ → ℝ) (hsmall : Tendsto H atTop (𝓝 0))
    (h : ∀ m, κ m → ℝ) (hdiam : ∀ m T i j, ‖b m T i - b m T j‖ ≤ h m T)
    (hmax : ∀ m T, h m T ≤ H m)
    (hshape : ∀ m T, h m T * ∑ i, ‖affineBasisCoordinateDerivative (b m T) i‖ ≤ C) :
    Tendsto (fun m => physicalMeshH1Element (b m) (hb m) (hboundary m) n hn φ.1
      (zero_frontier_of_tsupport_subset_interior (b m)
        (by simpa only [hsets m] using φ.2.2.2.trans hΩS)) hΩ)
      atTop (𝓝 (physicalH1OfTest hΩ φ)) := by
  obtain ⟨M, hM⟩ := exists_lipschitzWith_fderiv_physicalTest φ
  have herr := tendsto_physicalMeshRecovery_H1_error b hb S hsets n hn φ.1 M C
    M.coe_nonneg hC H hsmall h hdiam hmax hshape
    (fun z _ => φ.2.1.differentiable (by simp) z)
    (fun y _ z _ => hM.norm_sub_le y z)
  have hsub : Ω ⊆ S := hΩS.trans interior_subset
  have hf := tendsto_eLpNorm_restrict_of_subset hsub herr.1
  have hg := tendsto_eLpNorm_restrict_of_subset hsub herr.2
  apply (tendsto_physicalH1OfWitness_iff _ (physicalTestH1Witness hΩ φ)).mpr
  exact ⟨hf, fun i => tendsto_eLpNorm_component_of_vector hg i⟩

/-- When the actual recovered supports stay inside Ω, the same recovery
converges strongly in the concrete H01 closed Hilbert subspace. This covers
smooth interior test inputs; full-cone positive density remains separate. -/
theorem tendsto_physicalMeshH01Element
    {κ : ℕ → Type*} [∀ m, Finite (κ m)]
    (b : ∀ m, κ m → AffineBasis (Fin (d + 1)) ℝ E)
    (hb : ∀ m, physicalFacesMatch (b m)) (hboundary : ∀ m, physicalBoundaryFaces (b m))
    (S : Set E) (hsets : ∀ m, physicalMeshSet (b m) = S)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ interior S)
    (n : ℕ) (hn : 0 < n) (φ : PhysicalSobolevTest Ω)
    (C : ℝ) (hC : 0 ≤ C) (H : ℕ → ℝ) (hsmall : Tendsto H atTop (𝓝 0))
    (h : ∀ m, κ m → ℝ) (hdiam : ∀ m T i j, ‖b m T i - b m T j‖ ≤ h m T)
    (hmax : ∀ m T, h m T ≤ H m)
    (hshape : ∀ m T, h m T * ∑ i, ‖affineBasisCoordinateDerivative (b m T) i‖ ≤ C)
    (hs : ∀ m, tsupport (physicalMeshRecovery (b m) n hn φ.1) ⊆ Ω) :
    Tendsto (fun m => physicalMeshH01Element (b m) (hb m) (hboundary m) n hn φ.1
      (zero_frontier_of_tsupport_subset_interior (b m)
        (by simpa only [hsets m] using φ.2.2.2.trans hΩS)) hΩ (hs m))
      atTop (𝓝 (physicalH01OfTest hΩ φ)) := by
  rw [tendsto_subtype_rng]
  exact tendsto_physicalMeshH1Element b hb hboundary S hsets hΩ hΩS n hn φ C hC
    H hsmall h hdiam hmax hshape

/-- A concrete H01 recovery on every mesh index: use the actual assembled
sampler when its support is inside Ω and zero otherwise. For each fixed
interior input the zero branch disappears on all sufficiently fine meshes. -/
def physicalSupportedMeshH01Recovery {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0) {Ω : Set E} (hΩ : IsOpen Ω) :
    physicalH01Submodule Ω hΩ := by
  classical
  exact if hs : tsupport (physicalMeshRecovery b n hn f) ⊆ Ω then
    physicalMeshH01Element b hb hboundary n hn f hf hΩ hs
  else 0

theorem eventually_tsupport_physicalMeshRecovery_subset
    {κ : ℕ → Type*} [∀ m, Finite (κ m)]
    (b : ∀ m, κ m → AffineBasis (Fin (d + 1)) ℝ E)
    (hb : ∀ m, physicalFacesMatch (b m)) {Ω : Set E} (hΩ : IsOpen Ω)
    (φ : PhysicalSobolevTest Ω) (n : ℕ) (hn : 0 < n)
    (H : ℕ → ℝ) (hsmall : Tendsto H atTop (𝓝 0))
    (hdiam : ∀ m T i j, ‖b m T i - b m T j‖ ≤ H m) :
    ∀ᶠ m in atTop, tsupport (physicalMeshRecovery (b m) n hn φ.1) ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := φ.2.2.1.isCompact.exists_cthickening_subset_open hΩ φ.2.2.2
  filter_upwards [hsmall.eventually (gt_mem_nhds hδ)] with m hm
  exact (tsupport_physicalMeshRecovery_subset_cthickening (b m) (hb m) n hn φ.1
    (H m) (hdiam m)).trans ((Metric.cthickening_mono hm.le (tsupport φ.1)).trans hδΩ)

/-- Strong H01 recovery of every fixed smooth interior input with no
recovered-support or H01-membership witness supplied for any mesh index.
The operator is actual Bernstein recovery eventually and zero before that. -/
theorem tendsto_physicalSupportedMeshH01Recovery
    {κ : ℕ → Type*} [∀ m, Finite (κ m)]
    (b : ∀ m, κ m → AffineBasis (Fin (d + 1)) ℝ E)
    (hb : ∀ m, physicalFacesMatch (b m)) (hboundary : ∀ m, physicalBoundaryFaces (b m))
    (S : Set E) (hsets : ∀ m, physicalMeshSet (b m) = S)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ interior S)
    (n : ℕ) (hn : 0 < n) (φ : PhysicalSobolevTest Ω)
    (C : ℝ) (hC : 0 ≤ C) (H : ℕ → ℝ) (hsmall : Tendsto H atTop (𝓝 0))
    (h : ∀ m, κ m → ℝ) (hdiam : ∀ m T i j, ‖b m T i - b m T j‖ ≤ h m T)
    (hmax : ∀ m T, h m T ≤ H m)
    (hshape : ∀ m T, h m T * ∑ i, ‖affineBasisCoordinateDerivative (b m T) i‖ ≤ C) :
    Tendsto (fun m => physicalSupportedMeshH01Recovery (b m) (hb m) (hboundary m) n hn φ.1
      (zero_frontier_of_tsupport_subset_interior (b m)
        (by simpa only [hsets m] using φ.2.2.2.trans hΩS)) hΩ)
      atTop (𝓝 (physicalH01OfTest hΩ φ)) := by
  apply tendsto_subtype_rng.mpr
  have hconv := tendsto_physicalMeshH1Element b hb hboundary S hsets hΩ hΩS n hn φ C hC
    H hsmall h hdiam hmax hshape
  apply hconv.congr'
  filter_upwards [eventually_tsupport_physicalMeshRecovery_subset b hb hΩ φ n hn H hsmall
    (fun m T i j => (hdiam m T i j).trans (hmax m T))] with m hm
  simp only [physicalSupportedMeshH01Recovery, dif_pos hm]
  rfl

theorem physicalSupportedMeshH01Recovery_mem_nonnegative {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0) {Ω : Set E} (hΩ : IsOpen Ω)
    (hpos : ∀ p ∈ physicalMeshSet b, 0 ≤ f p) :
    physicalSupportedMeshH01Recovery b hb hboundary n hn f hf hΩ ∈
      physicalNonnegativeH01Cone Ω hΩ := by
  classical
  unfold physicalSupportedMeshH01Recovery
  split_ifs with hs
  · exact physicalMeshH01Element_mem_nonnegative b hb hboundary n hn f hf hΩ hs hpos
  · change 0 ≤ physicalH01FunctionLp Ω hΩ 0
    simp only [map_zero, le_refl]

end

end BernsteinObstacle
