import BernsteinObstacle.PhysicalLpIndicator

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal BigOperators

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual cell polynomial, cut off at its compact physical cell,
belongs to L2 on any domain. No global polynomial-integrability assumption. -/
theorem memLp_physicalCellField (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    (Ω : Set E) (c : MultiIndex d n → ℝ) :
    MemLp ((Set.range (physicalSimplexPoint b)).indicator (physicalBernsteinField b n c))
      2 (volume.restrict Ω) := by
  have hM : MemLp (physicalBernsteinField b n c) 2
      (volume.restrict (Set.range (physicalSimplexPoint b))) :=
    memLp_continuous_restrict_compact 2 (isCompact_range_physicalSimplexPoint_affineBasis b)
      (contDiff_affineSimplexField 0 d n (affineBasisCoordinateConstant b)
        (affineBasisCoordinateDerivative b) c).continuous volume
  exact ((memLp_indicator_iff_restrict (measurableSet_range_physicalSimplexPoint_affineBasis b)).mpr hM).mono_measure
    Measure.restrict_le_self

def physicalCellFieldLp (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    (Ω : Set E) (c : MultiIndex d n → ℝ) : Lp ℝ 2 (volume.restrict Ω) :=
  (memLp_physicalCellField b n Ω c).toLp
    ((Set.range (physicalSimplexPoint b)).indicator (physicalBernsteinField b n c))

theorem physicalCellFieldLp_coe (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    (Ω : Set E) (c : MultiIndex d n → ℝ) :
    physicalCellFieldLp b n Ω c =ᵐ[volume.restrict Ω]
      (Set.range (physicalSimplexPoint b)).indicator (physicalBernsteinField b n c) :=
  (memLp_physicalCellField b n Ω c).coeFn_toLp

set_option backward.isDefEq.respectTransparency false in
/-- The genuine coefficient-to-cell-L2 linear map. Assembly and zero trace
are still imposed by the surrounding H01 space, not by this local map. -/
def physicalCellCoefficientMap (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (Ω : Set E) :
    (MultiIndex d n → ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω) where
  toFun := physicalCellFieldLp b n Ω
  map_add' := by
    intro c e
    apply Lp.ext
    filter_upwards [physicalCellFieldLp_coe b n Ω (c + e),
      Lp.coeFn_add (physicalCellFieldLp b n Ω c) (physicalCellFieldLp b n Ω e),
      physicalCellFieldLp_coe b n Ω c, physicalCellFieldLp_coe b n Ω e]
      with x hleft hright hc he
    rw [hleft, hright, Pi.add_apply, hc, he]
    by_cases hx : x ∈ Set.range (physicalSimplexPoint b)
    · simp only [Set.indicator_of_mem hx]
      have hlin := physicalBernsteinField_linear_coefficients b n c e 1 1 x
      simp only [one_mul] at hlin
      convert! hlin using 1 <;> rfl
    · simp [hx]
  map_smul' := by
    intro r c
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [physicalCellFieldLp_coe b n Ω (r • c),
      Lp.coeFn_smul r (physicalCellFieldLp b n Ω c), physicalCellFieldLp_coe b n Ω c]
      with x hleft hright hc
    rw [hleft, hright, Pi.smul_apply, hc]
    by_cases hx : x ∈ Set.range (physicalSimplexPoint b)
    · simp only [Set.indicator_of_mem hx]
      have hlin := physicalBernsteinField_linear_coefficients b n c (fun _ => 0) r 0 x
      simp only [zero_mul, add_zero] at hlin
      convert! hlin using 1 <;> rfl
    · simp [hx]

def physicalCellBasisLp (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ) (Ω : Set E)
    (α : MultiIndex d n) : Lp ℝ 2 (volume.restrict Ω) := by
  classical
  exact physicalCellFieldLp b n Ω (Pi.single α 1)

theorem physicalCellFieldLp_eq_sum_basis (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    (Ω : Set E) (c : MultiIndex d n → ℝ) :
    physicalCellFieldLp b n Ω c = ∑ α, c α • physicalCellBasisLp b n Ω α := by
  classical
  have hdec : c = ∑ α, c α • Pi.single α (1 : ℝ) := by
    ext β
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  calc
    physicalCellFieldLp b n Ω c = physicalCellCoefficientMap b n Ω c := rfl
    _ = physicalCellCoefficientMap b n Ω (∑ α, c α • Pi.single α (1 : ℝ)) :=
      congrArg (physicalCellCoefficientMap b n Ω) hdec
    _ = _ := by simp only [map_sum, map_smul]; rfl

theorem physicalCellBasisLp_nonneg (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    (Ω : Set E) (α : MultiIndex d n) : 0 ≤ physicalCellBasisLp b n Ω α := by
  classical
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [physicalCellFieldLp_coe b n Ω (Pi.single α 1)] with x hx
  change 0 ≤ physicalCellFieldLp b n Ω (Pi.single α 1) x
  rw [hx]
  by_cases hxs : x ∈ Set.range (physicalSimplexPoint b)
  · rw [Set.indicator_of_mem hxs]
    apply physicalBernsteinField_nonneg b n _ _ hxs
    intro β
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp [hxs]

set_option backward.isDefEq.respectTransparency false in
/-- A.e. local polynomial representation is equivalent to equality of
actual cell-indicator L2 classes. This respects arbitrary representatives. -/
theorem physicalCell_indicator_eq_iff (b : AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    {Ω : Set E} (hΩ : IsOpen Ω) (z : physicalH01Submodule Ω hΩ) (c : MultiIndex d n → ℝ) :
    physicalLpIndicator (Set.range (physicalSimplexPoint b))
      (measurableSet_range_physicalSimplexPoint_affineBasis b) (physicalH01FunctionLp Ω hΩ z) =
        physicalCellFieldLp b n Ω c ↔
      ∀ᵐ x ∂volume.restrict Ω, x ∈ Set.range (physicalSimplexPoint b) →
        z.1.1 0 x = physicalBernsteinField b n c x := by
  have hfun : physicalH01FunctionLp Ω hΩ z = z.1.1 0 := rfl
  constructor
  · intro heq
    filter_upwards [physicalLpIndicator_coe (Set.range (physicalSimplexPoint b))
        (measurableSet_range_physicalSimplexPoint_affineBasis b) (physicalH01FunctionLp Ω hΩ z),
      physicalCellFieldLp_coe b n Ω c] with x hz hc hx
    rw [heq] at hz
    simpa only [Set.indicator_of_mem hx, hfun] using hz.symm.trans hc
  · intro heq
    apply Lp.ext
    filter_upwards [heq, physicalLpIndicator_coe (Set.range (physicalSimplexPoint b))
        (measurableSet_range_physicalSimplexPoint_affineBasis b) (physicalH01FunctionLp Ω hΩ z),
      physicalCellFieldLp_coe b n Ω c] with x he hz hc
    rw [hz, hc]
    by_cases hx : x ∈ Set.range (physicalSimplexPoint b)
    · simpa only [Set.indicator_of_mem hx, hfun] using he hx
    · simp [hx]

theorem mem_physicalBernsteinH01Cone_iff_cell_cones {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    {Ω : Set E} (hΩ : IsOpen Ω) (z : physicalH01Submodule Ω hΩ) :
    z ∈ physicalBernsteinH01Cone b n Ω hΩ ↔
      ∀ T, physicalLpIndicator (Set.range (physicalSimplexPoint (b T)))
        (measurableSet_range_physicalSimplexPoint_affineBasis (b T))
        (physicalH01FunctionLp Ω hΩ z) ∈ positiveFiniteLpCone (physicalCellBasisLp (b T) n Ω) := by
  classical
  constructor
  · rintro ⟨c, hc, he⟩ T
    refine ⟨c T, hc T, ?_⟩
    exact (physicalCell_indicator_eq_iff (b T) n hΩ z (c T)).mpr (he T) |>.trans
      (physicalCellFieldLp_eq_sum_basis (b T) n Ω (c T))
  · intro h
    change ∀ T, ∃ c : MultiIndex d n → ℝ, (∀ α, 0 ≤ c α) ∧
      physicalLpIndicator (Set.range (physicalSimplexPoint (b T)))
        (measurableSet_range_physicalSimplexPoint_affineBasis (b T))
        (physicalH01FunctionLp Ω hΩ z) = ∑ α, c α • physicalCellBasisLp (b T) n Ω α at h
    choose c hc he using h
    refine ⟨c, hc, fun T => (physicalCell_indicator_eq_iff (b T) n hΩ z (c T)).mp ?_⟩
    exact (he T).trans (physicalCellFieldLp_eq_sum_basis (b T) n Ω (c T)).symm

/-- The intrinsic actual Bernstein coefficient cone is norm closed in
H01. Each cell condition is the continuous preimage of a proved closed
finite nonnegative L2 cone; their intersection enforces every cell. Neither
linear independence nor a discrete closedness oracle is assumed. -/
theorem isClosed_physicalBernsteinH01Cone {ι : Type*}
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    {Ω : Set E} (hΩ : IsOpen Ω) : IsClosed (physicalBernsteinH01Cone b n Ω hΩ) := by
  let Q : ι → physicalH01Submodule Ω hΩ → Lp ℝ 2 (volume.restrict Ω) := fun T z =>
    physicalLpIndicator (Set.range (physicalSimplexPoint (b T)))
      (measurableSet_range_physicalSimplexPoint_affineBasis (b T)) (physicalH01FunctionLp Ω hΩ z)
  have heq : physicalBernsteinH01Cone b n Ω hΩ =
      ⋂ T, (Q T) ⁻¹' positiveFiniteLpCone (physicalCellBasisLp (b T) n Ω) := by
    ext z
    simpa only [Set.mem_iInter, Set.mem_preimage] using
      mem_physicalBernsteinH01Cone_iff_cell_cones b n hΩ z
  rw [heq]
  apply isClosed_iInter
  intro T
  apply (isClosed_positiveFiniteLpCone (physicalCellBasisLp (b T) n Ω)
    (physicalCellBasisLp_nonneg (b T) n Ω)).preimage
  exact (physicalLpIndicatorCLM (Set.range (physicalSimplexPoint (b T)))
    (measurableSet_range_physicalSimplexPoint_affineBasis (b T))).continuous.comp
      (physicalH01FunctionLp Ω hΩ).continuous

end

end BernsteinObstacle
