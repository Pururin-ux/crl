import BernsteinObstacle.PhysicalConeDensity

open MeasureTheory Set Function Filter Topology

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual degree-n Bernstein polynomial on a physical affine-basis cell. -/
def physicalBernsteinField (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    (c : MultiIndex d n → ℝ) : E → ℝ :=
  affineSimplexField d n (affineBasisCoordinateConstant b) (affineBasisCoordinateDerivative b) c

theorem physicalBernsteinField_nonneg
    (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (c : MultiIndex d n → ℝ)
    (hc : ∀ α, 0 ≤ c α) {p : E} (hp : p ∈ Set.range (physicalSimplexPoint b)) :
    0 ≤ physicalBernsteinField b n c p := by
  obtain ⟨x, rfl⟩ := hp
  rw [physicalBernsteinField, affineSimplexField_eq_simplexField d n _ _ _ _ x
    (affineBasisCoordinate_physicalSimplexPoint b x)]
  exact simplexField_nonneg d n c hc x

/-- The actual conforming coefficient cone inside H01: its represented
function is, on each physical cell, the actual Bernstein polynomial with
nonnegative coefficients. H01 conformity and zero trace are properties of
the ambient space. Equalities are a.e. on Ω, so this definition is invariant
under the choice of L2 representative and does not sample an arbitrary H1
equivalence class. This is the full local coefficient cone, not just an image
of positive smooth inputs under the recovery operator. -/
def physicalBernsteinH01Cone {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    (Ω : Set E) (hΩ : IsOpen Ω) : Set (physicalH01Submodule Ω hΩ) :=
  {z | ∃ c : ι → MultiIndex d n → ℝ,
    (∀ T α, 0 ≤ c T α) ∧ ∀ T, ∀ᵐ x ∂volume.restrict Ω,
      x ∈ Set.range (physicalSimplexPoint (b T)) →
        z.1.1 0 x = physicalBernsteinField (b T) n (c T) x}

theorem zero_mem_physicalBernsteinH01Cone {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    {Ω : Set E} (hΩ : IsOpen Ω) :
    (0 : physicalH01Submodule Ω hΩ) ∈ physicalBernsteinH01Cone b n Ω hΩ := by
  refine ⟨fun _ _ => 0, fun _ _ => le_refl 0, ?_⟩
  intro T
  change ∀ᵐ x ∂volume.restrict Ω, x ∈ Set.range (physicalSimplexPoint (b T)) →
    (0 : Lp ℝ 2 (volume.restrict Ω)) x = physicalBernsteinField (b T) n (fun _ => 0) x
  filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx _hp
  simpa only [physicalBernsteinField, affineSimplexField, zero_mul,
    Finset.sum_const_zero, Pi.zero_apply] using hx

theorem physicalBernsteinH01Cone_subset_nonnegative {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    {Ω : Set E} (hΩ : IsOpen Ω) (hcover : Ω ⊆ physicalMeshSet b) :
    physicalBernsteinH01Cone b n Ω hΩ ⊆ physicalNonnegativeH01Cone Ω hΩ := by
  rintro z ⟨c, hc, heq⟩
  apply (mem_physicalNonnegativeH01Cone_iff hΩ z).mpr
  have hall : ∀ᵐ x ∂volume.restrict Ω, ∀ T,
      x ∈ Set.range (physicalSimplexPoint (b T)) →
        z.1.1 0 x = physicalBernsteinField (b T) n (c T) x := ae_all_iff.mpr heq
  filter_upwards [hall, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  obtain ⟨T, hxT⟩ := mem_iUnion.mp (hcover hxΩ)
  rw [hx T hxT]
  exact physicalBernsteinField_nonneg (b T) n (c T) (hc T) hxT

theorem physicalMeshH01Element_mem_coefficientCone {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0)
    {Ω : Set E} (hΩ : IsOpen Ω) (hs : tsupport (physicalMeshRecovery b n hn f) ⊆ Ω)
    (hpos : ∀ p ∈ physicalMeshSet b, 0 ≤ f p) :
    physicalMeshH01Element b hb hboundary n hn f hf hΩ hs ∈
      physicalBernsteinH01Cone b n Ω hΩ := by
  let c : ι → MultiIndex d n → ℝ := fun T => simplexSamplingCoefficients d n hn
    (fun y => f (physicalSimplexPoint (b T) y))
  refine ⟨c, ?_, ?_⟩
  · intro T α
    exact simplexSamplingCoefficients_nonneg d n hn _
      (fun y => hpos _ (mem_iUnion.mpr ⟨T, y, rfl⟩)) α
  · intro T
    let hw := physicalMeshH1Witness b hb hboundary n hn f hf hΩ
    change ∀ᵐ x ∂volume.restrict Ω, x ∈ Set.range (physicalSimplexPoint (b T)) →
      hw.memLp.toLp (physicalMeshRecovery b n hn f) x = physicalBernsteinField (b T) n (c T) x
    filter_upwards [hw.memLp.coeFn_toLp] with x hx hxT
    rw [hx, physicalMeshRecovery_eq_on_element b hb n hn f T x hxT]
    rfl

theorem physicalSupportedMeshH01Recovery_mem_coefficientCone {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0) {Ω : Set E} (hΩ : IsOpen Ω)
    (hpos : ∀ p ∈ physicalMeshSet b, 0 ≤ f p) :
    physicalSupportedMeshH01Recovery b hb hboundary n hn f hf hΩ ∈
      physicalBernsteinH01Cone b n Ω hΩ := by
  classical
  unfold physicalSupportedMeshH01Recovery
  split_ifs with hs
  · exact physicalMeshH01Element_mem_coefficientCone b hb hboundary n hn f hf hΩ hs hpos
  · exact zero_mem_physicalBernsteinH01Cone b n hΩ

end

end BernsteinObstacle
