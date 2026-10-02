import BernsteinObstacle.PhysicalZeroTraceSpace
import BernsteinObstacle.ConvexWeakClosure
import Mathlib.MeasureTheory.Function.LpOrder

open MeasureTheory Set Function Filter Topology
open scoped ENNReal

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual L2 function coordinate of a concrete H01 element, as a
continuous linear map. Neither a trace map nor a Sobolev embedding is assumed. -/
def physicalH01FunctionLp (Ω : Set E) (hΩ : IsOpen Ω) :
    physicalH01Submodule Ω hΩ →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (PiLp.proj 2 _ 0).comp
    ((physicalH1Submodule Ω).subtypeL.comp (physicalH01Submodule Ω hΩ).subtypeL)

/-- The full nonnegative cone in the actual physical H01 Hilbert space,
defined by almost-everywhere order of the represented L2 function. -/
def physicalNonnegativeH01Cone (Ω : Set E) (hΩ : IsOpen Ω) :
    Set (physicalH01Submodule Ω hΩ) :=
  {z | 0 ≤ physicalH01FunctionLp Ω hΩ z}

theorem mem_physicalNonnegativeH01Cone_iff {Ω : Set E} (hΩ : IsOpen Ω)
    (z : physicalH01Submodule Ω hΩ) :
    z ∈ physicalNonnegativeH01Cone Ω hΩ ↔ ∀ᵐ x ∂volume.restrict Ω, 0 ≤ z.1.1 0 x :=
  (Lp.coeFn_nonneg (physicalH01FunctionLp Ω hΩ z)).symm

/-- The real L2 order is closed in its norm topology; the function
coordinate is continuous, so the actual H01 nonnegative cone is norm closed. -/
theorem isClosed_physicalNonnegativeH01Cone (Ω : Set E) (hΩ : IsOpen Ω) :
    IsClosed (physicalNonnegativeH01Cone Ω hΩ) := by
  change IsClosed ((physicalH01FunctionLp Ω hΩ) ⁻¹' Ici (0 : Lp ℝ 2 (volume.restrict Ω)))
  exact isClosed_Ici.preimage (physicalH01FunctionLp Ω hΩ).continuous

theorem convex_physicalNonnegativeH01Cone (Ω : Set E) (hΩ : IsOpen Ω) :
    Convex ℝ (physicalNonnegativeH01Cone Ω hΩ) := by
  intro z hz w hw a b ha hb _hab
  change 0 ≤ physicalH01FunctionLp Ω hΩ (a • z + b • w)
  simp only [map_add, map_smul]
  apply (Lp.coeFn_nonneg _).mp
  have hz' := (mem_physicalNonnegativeH01Cone_iff hΩ z).mp hz
  have hw' := (mem_physicalNonnegativeH01Cone_iff hΩ w).mp hw
  filter_upwards [hz', hw',
    Lp.coeFn_add (a • physicalH01FunctionLp Ω hΩ z) (b • physicalH01FunctionLp Ω hΩ w),
    Lp.coeFn_smul a (physicalH01FunctionLp Ω hΩ z),
    Lp.coeFn_smul b (physicalH01FunctionLp Ω hΩ w)] with x hzx hwx hadd hza hwb
  rw [hadd, Pi.add_apply, hza, hwb, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha hzx) (mul_nonneg hb hwx)

/-- The weak-limit condition is proved for the actual full physical H01
cone, using its proved convexity and norm closedness. Strong full-cone
Bernstein recovery remains a distinct proof obligation. -/
theorem weaklySequentiallyClosed_physicalNonnegativeH01Cone (Ω : Set E) (hΩ : IsOpen Ω) :
    WeaklySequentiallyClosed (physicalNonnegativeH01Cone Ω hΩ) :=
  weaklySequentiallyClosed_of_convex_isClosed _
    (convex_physicalNonnegativeH01Cone Ω hΩ) (isClosed_physicalNonnegativeH01Cone Ω hΩ)

variable [NeZero d]

/-- The actual H01 embedding preserves precisely almost-everywhere
nonnegativity of the underlying function; no pointwise representative is assumed. -/
theorem physicalH01OfWitness_mem_nonnegative_iff {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : SobolevH01Port.MemW1pWitness 2 u Ω) (hu : SobolevH01Port.MemH01 u Ω) :
    physicalH01OfWitness hΩ hw hu ∈ physicalNonnegativeH01Cone Ω hΩ ↔
      ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u x := by
  rw [mem_physicalNonnegativeH01Cone_iff]
  change (∀ᵐ x ∂volume.restrict Ω, 0 ≤ hw.memLp.toLp u x) ↔ _
  constructor
  · intro h
    filter_upwards [h, hw.memLp.coeFn_toLp] with x hx heq
    simpa only [heq] using hx
  · intro h
    filter_upwards [h, hw.memLp.coeFn_toLp] with x hx heq
    simpa only [heq] using hx

/-- A nonnegative actual sampler, with proved geometric assembly and
interior-supported zero trace, belongs to the concrete physical H01 cone. -/
theorem physicalMeshH01Element_mem_nonnegative {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (hb : physicalFacesMatch b)
    (hboundary : physicalBoundaryFaces b) (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ p ∈ frontier (physicalMeshSet b), f p = 0)
    {Ω : Set E} (hΩ : IsOpen Ω) (hs : tsupport (physicalMeshRecovery b n hn f) ⊆ Ω)
    (hpos : ∀ p ∈ physicalMeshSet b, 0 ≤ f p) :
    physicalMeshH01Element b hb hboundary n hn f hf hΩ hs ∈
      physicalNonnegativeH01Cone Ω hΩ := by
  apply (physicalH01OfWitness_mem_nonnegative_iff hΩ _ _).mpr
  exact Eventually.of_forall (physicalMeshRecovery_nonneg b hb n hn f hpos)

end

end BernsteinObstacle
