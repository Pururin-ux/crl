import BernsteinObstacle.PhysicalMosco

open MeasureTheory Set Function Filter Topology Metric

namespace BernsteinObstacle

noncomputable section

/-- Nonnegative affine coordinates on a genuine inscribed ball bound their
actual linear derivative. This is the geometric scaling step used below. -/
theorem norm_affine_derivative_le_of_inscribed_ball
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : ℝ) (L : X →L[ℝ] ℝ) (c : X) (r : ℝ) (hr : 0 < r)
    (hball : ∀ p ∈ closedBall c r, a + L p ∈ Icc (0 : ℝ) 1) :
    ‖L‖ ≤ 1 / r := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let s : ℝ := r / ‖v‖
  have hs : 0 < s := div_pos hr hnv
  have hrad : ‖s • v‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hs.le]
    exact div_mul_cancel₀ r hnv.ne'
  have hp : c + s • v ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hrad]
  have hm : c - s • v ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, hrad]
  have hcp : a + L c ≤ 1 := (hball c (mem_closedBall_self hr.le)).2
  have hplus := (hball (c + s • v) hp).1
  have hminus := (hball (c - s • v) hm).1
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at hplus hminus
  have habs : s * |L v| ≤ 1 := by
    rw [← abs_of_pos hs, ← abs_mul]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Real.norm_eq_abs]
  have hscaled : |L v| ≤ 1 / s := (le_div_iff₀ hs).2 (by nlinarith [habs])
  calc
    |L v| ≤ 1 / s := hscaled
    _ = (1 / r) * ‖v‖ := by dsimp [s]; field_simp

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem affineBasisCoordinate_mem_Icc
    (b : AffineBasis (Fin (d + 1)) ℝ E) {p : E}
    (hp : p ∈ Set.range (physicalSimplexPoint b)) (i : Fin (d + 1)) :
    affineBasisCoordinateConstant b i + affineBasisCoordinateDerivative b i p ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨x, rfl⟩ := hp
  rw [affineBasisCoordinate_physicalSimplexPoint b x]
  refine ⟨x.2.1 i, ?_⟩
  calc
    x.1 i ≤ ∑ j, x.1 j := Finset.single_le_sum (fun j _ => x.2.1 j) (Finset.mem_univ i)
    _ = 1 := x.2.2

/-- A physical cell containing an actual ball of radius r has the uniform
coordinate estimate h * sum_i ||D lambda_i|| <= (d+1) * sigma when h/r<=sigma.
Thus the previously explicit coordinate shape hypothesis follows from the
usual geometric diameter-to-inscribed-radius bound. No quasi-uniformity is
used, and the radius need not be the maximal inradius. -/
theorem physical_coordinate_shape_of_inscribed_ball
    (b : AffineBasis (Fin (d + 1)) ℝ E) (c : E) (r h σ : ℝ)
    (hr : 0 < r) (hh : 0 ≤ h)
    (hball : closedBall c r ⊆ Set.range (physicalSimplexPoint b)) (hshape : h / r ≤ σ) :
    h * ∑ i, ‖affineBasisCoordinateDerivative b i‖ ≤ (d + 1 : ℝ) * σ := by
  have hbound (i : Fin (d + 1)) : ‖affineBasisCoordinateDerivative b i‖ ≤ 1 / r :=
    norm_affine_derivative_le_of_inscribed_ball (affineBasisCoordinateConstant b i)
      (affineBasisCoordinateDerivative b i) c r hr
      (fun p hp => affineBasisCoordinate_mem_Icc b (hball hp) i)
  calc
    h * ∑ i, ‖affineBasisCoordinateDerivative b i‖ ≤ h * ∑ _i : Fin (d + 1), (1 / r) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbound i) hh
    _ = (d + 1 : ℝ) * (h / r) := by simp; ring
    _ ≤ (d + 1 : ℝ) * σ := mul_le_mul_of_nonneg_left hshape (by positivity)

/-- Actual physical Mosco theorem under geometric ball-based shape
regularity. Here r is a radius; a convention using the inscribed-ball
diameter has shape constant half of σ. Each local coordinate estimate is
derived by the preceding theorem, rather than supplied as an oracle. The
mesh family, conformity and common-set geometry remain explicit inputs. -/
theorem mosco_physicalBernsteinH01Cone_of_inscribed_balls
    {κ : ℕ → Type*} [∀ m, Finite (κ m)]
    (b : ∀ m, κ m → AffineBasis (Fin (d + 1)) ℝ E)
    (hb : ∀ m, physicalFacesMatch (b m)) (hboundary : ∀ m, physicalBoundaryFaces (b m))
    (S : Set E) (hsets : ∀ m, physicalMeshSet (b m) = S)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ interior S)
    (n : ℕ) (hn : 0 < n)
    (H : ℕ → ℝ) (hsmall : Tendsto H atTop (𝓝 0))
    (h : ∀ m, κ m → ℝ) (hdiam : ∀ m T i j, ‖b m T i - b m T j‖ ≤ h m T)
    (hmax : ∀ m T, h m T ≤ H m)
    (c : ∀ m, κ m → E) (r : ∀ m, κ m → ℝ) (hr : ∀ m T, 0 < r m T)
    (hball : ∀ m T, closedBall (c m T) (r m T) ⊆ Set.range (physicalSimplexPoint (b m T)))
    (σ : ℝ) (hσ : 0 ≤ σ) (hshape : ∀ m T, h m T / r m T ≤ σ) :
    MoscoConverges (fun m => physicalBernsteinH01Cone (b m) n Ω hΩ)
      (physicalNonnegativeH01Cone Ω hΩ) := by
  apply mosco_physicalBernsteinH01Cone b hb hboundary S hsets hΩ hΩS n hn
    ((d + 1 : ℝ) * σ) (mul_nonneg (by positivity) hσ) H hsmall h hdiam hmax
  intro m T
  have hh : 0 ≤ h m T := by simpa only [sub_self, norm_zero] using hdiam m T 0 0
  exact physical_coordinate_shape_of_inscribed_ball (b m T) (c m T) (r m T) (h m T) σ
    (hr m T) hh (hball m T) (hshape m T)

end

end BernsteinObstacle
