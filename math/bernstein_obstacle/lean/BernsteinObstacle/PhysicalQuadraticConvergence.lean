import BernsteinObstacle.PhysicalBernsteinExistence

/-!
General symmetric continuous coercive quadratic energies on the actual H01
space. The midpoint identity proves a genuine minimizer energy-gap bound;
inner-cone recovery then gives strong convergence. No norm-error, weak
compactness, existence or convergence oracle is supplied. The physical mesh
geometry remains explicit, as in the Dirichlet specialization.
-/

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal BigOperators

namespace BernsteinObstacle

noncomputable section

theorem inverse_bound_of_coercive_bilin {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : IsCoercive B) :
    ∃ C : ℝ, 0 < C ∧ ∀ u, ‖u‖ ^ 2 ≤ C * B u u := by
  obtain ⟨μ, hμ, hbound⟩ := hB
  refine ⟨μ⁻¹, inv_pos.mpr hμ, ?_⟩
  intro u
  have hb : μ * ‖u‖ ^ 2 ≤ B u u := by
    simpa only [pow_two, mul_assoc] using hbound u
  have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hμ.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul] using hm

def IsCoerciveQuadraticMinimizer {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ) (K : Set X) (u : X) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, coerciveQuadraticEnergy B F u ≤ coerciveQuadraticEnergy B F v

/-- Minimality at the feasible midpoint and actual coercivity bound the full
norm error by the energy gap. The factor four is a safe qualitative constant;
this is not the sharp free-boundary clipping estimate. -/
theorem coerciveQuadraticMinimizer_norm_sq_le_energy_gap {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ u, ‖u‖ ^ 2 ≤ C * B u u)
    (hsymm : ∀ u v, B u v = B v u)
    (K : Set X) (hK : Convex ℝ K) (u v : X)
    (hu : IsCoerciveQuadraticMinimizer B F K u) (hv : v ∈ K) :
    ‖v - u‖ ^ 2 ≤ 4 * C *
      (coerciveQuadraticEnergy B F v - coerciveQuadraticEnergy B F u) := by
  have hm : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v ∈ K :=
    hK hu.1 hv (by norm_num) (by norm_num) (by norm_num)
  have hmin := hu.2 _ hm
  have hid := coerciveQuadraticEnergy_midpoint B F hsymm u v
  have hgap : B (u - v) (u - v) ≤
      4 * (coerciveQuadraticEnergy B F v - coerciveQuadraticEnergy B F u) := by
    nlinarith
  calc
    ‖v - u‖ ^ 2 = ‖u - v‖ ^ 2 := by rw [norm_sub_rev]
    _ ≤ C * B (u - v) (u - v) := hbound (u - v)
    _ ≤ C * (4 * (coerciveQuadraticEnergy B F v - coerciveQuadraticEnergy B F u)) :=
      mul_le_mul_of_nonneg_left hgap hC.le
    _ = _ := by ring

theorem coerciveQuadraticMinimizer_unique {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ u, ‖u‖ ^ 2 ≤ C * B u u)
    (hsymm : ∀ u v, B u v = B v u)
    (K : Set X) (hK : Convex ℝ K) (u v : X)
    (hu : IsCoerciveQuadraticMinimizer B F K u)
    (hv : IsCoerciveQuadraticMinimizer B F K v) : u = v := by
  have herr := coerciveQuadraticMinimizer_norm_sq_le_energy_gap
    B F C hC hbound hsymm K hK u v hu hv.1
  have hmin := hv.2 u hu.1
  have hnorm : ‖v - u‖ = 0 := by
    have hn := norm_nonneg (v - u)
    have hc : 0 ≤ 4 * C := by positivity
    have hle : 4 * C *
        (coerciveQuadraticEnergy B F v - coerciveQuadraticEnergy B F u) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hmin)
    nlinarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

theorem existsUnique_coerciveQuadraticEnergy_minimizer {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ u, ‖u‖ ^ 2 ≤ C * B u u)
    (hsymm : ∀ u v, B u v = B v u)
    (K : Set X) (hne : K.Nonempty) (hclosed : IsClosed K) (hK : Convex ℝ K) :
    ∃! u, IsCoerciveQuadraticMinimizer B F K u := by
  obtain ⟨u, hu, hmin⟩ := exists_coerciveQuadraticEnergy_minimizer B F C hC hbound hsymm
    K hne hclosed.isComplete hK
  refine ⟨u, ⟨hu, hmin⟩, ?_⟩
  intro v hv
  exact coerciveQuadraticMinimizer_unique B F C hC hbound hsymm K hK v u hv ⟨hu, hmin⟩

/-- Inner feasible sets and strong feasible recovery imply convergence for
every continuous symmetric coercive quadratic energy. The error bound is
derived from actual energy minimality, not supplied as an assumption. -/
theorem tendsto_coerciveQuadraticMinimizers_of_inner_recovery {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (F : X →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ u, ‖u‖ ^ 2 ≤ C * B u u)
    (hsymm : ∀ u v, B u v = B v u)
    (K : Set X) (Kh : ℕ → Set X) (hK : Convex ℝ K) (hinner : ∀ m, Kh m ⊆ K)
    (u : X) (uh v : ℕ → X)
    (hu : IsCoerciveQuadraticMinimizer B F K u)
    (huh : ∀ m, IsCoerciveQuadraticMinimizer B F (Kh m) (uh m))
    (hv : ∀ m, v m ∈ Kh m) (hconv : Tendsto v atTop (𝓝 u)) :
    Tendsto uh atTop (𝓝 u) := by
  have herr (m : ℕ) : ‖uh m - u‖ ^ 2 ≤ 4 * C *
      (coerciveQuadraticEnergy B F (v m) - coerciveQuadraticEnergy B F u) := by
    have he := coerciveQuadraticMinimizer_norm_sq_le_energy_gap
      B F C hC hbound hsymm K hK u (uh m) hu (hinner m (huh m).1)
    have hc : 0 ≤ 4 * C := by positivity
    exact he.trans (mul_le_mul_of_nonneg_left
      (sub_le_sub_right ((huh m).2 (v m) (hv m)) _) hc)
  have hgap : Tendsto (fun m => coerciveQuadraticEnergy B F (v m) -
      coerciveQuadraticEnergy B F u) atTop (𝓝 0) := by
    simpa only [coerciveQuadraticEnergy, Function.comp_apply, sub_self] using
      ((continuous_quadratic_bilin_energy B F).tendsto u |>.comp hconv).sub_const
        (coerciveQuadraticEnergy B F u)
  have hs : Tendsto (fun m => ‖uh m - u‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun m => sq_nonneg _) herr (by simpa using hgap.const_mul (4 * C))
  have hnorm := Real.continuous_sqrt.tendsto 0 |>.comp hs
  have hnorm' : Tendsto (fun m => ‖uh m - u‖) atTop (𝓝 0) := by
    convert! hnorm using 1
    · ext m
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_zero]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm'

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The generic quadratic energy uses the actual inherited H01 norm and
scalar action, with the nested normed-space instance supplied explicitly. -/
def physicalQuadraticEnergy {Ω : Set E} (hΩ : IsOpen Ω)
    (B : physicalH01Submodule Ω hΩ →L[ℝ] physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ) (u : physicalH01Submodule Ω hΩ) : ℝ :=
  @coerciveQuadraticEnergy (physicalH01Submodule (d := d) Ω hΩ) inferInstance
    (physicalH01RealNormedSpace (d := d) hΩ) B F u

def IsPhysicalQuadraticMinimizer {Ω : Set E} (hΩ : IsOpen Ω)
    (B : physicalH01Submodule Ω hΩ →L[ℝ] physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (u : physicalH01Submodule Ω hΩ) : Prop :=
  @IsCoerciveQuadraticMinimizer (physicalH01Submodule (d := d) Ω hΩ) inferInstance
    (physicalH01RealNormedSpace (d := d) hΩ) B F K u

/-- The general physical energy specializes to the already constructed
genuine Dirichlet integral energy, with the same H01 space and norm. -/
theorem physicalQuadraticEnergy_dirichlet {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ) (u : physicalH01Submodule Ω hΩ) :
    physicalQuadraticEnergy hΩ (physicalDirichletBilin (d := d) hΩ) F u =
      physicalDirichletEnergy hΩ F u := rfl

theorem isPhysicalQuadraticMinimizer_dirichlet {Ω : Set E} (hΩ : IsOpen Ω)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (K : Set (physicalH01Submodule Ω hΩ)) (u : physicalH01Submodule Ω hΩ) :
    IsPhysicalQuadraticMinimizer hΩ (physicalDirichletBilin (d := d) hΩ) F K u ↔
      IsPhysicalDirichletMinimizer hΩ F K u := Iff.rfl

theorem existsUnique_physicalBernsteinQuadraticMinimizer {ι : Type*} [Finite ι]
    (b : ι → AffineBasis (Fin (d + 1)) ℝ E) (n : ℕ)
    {Ω : Set E} (hΩ : IsOpen Ω)
    (B : physicalH01Submodule Ω hΩ →L[ℝ] physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ u, ‖u‖ ^ 2 ≤ C * B u u)
    (hsymm : ∀ u v, B u v = B v u) :
    ∃! u, IsPhysicalQuadraticMinimizer hΩ B F (physicalBernsteinH01Cone b n Ω hΩ) u := by
  exact @existsUnique_coerciveQuadraticEnergy_minimizer (physicalH01Submodule (d := d) Ω hΩ)
    inferInstance (physicalH01RealNormedSpace (d := d) hΩ) inferInstance B F C hC hbound hsymm
    (physicalBernsteinH01Cone b n Ω hΩ) ⟨0, zero_mem_physicalBernsteinH01Cone b n hΩ⟩
    (isClosed_physicalBernsteinH01Cone b n hΩ) (convex_physicalBernsteinH01Cone b n hΩ)

theorem existsUnique_physicalNonnegativeQuadraticMinimizer {Ω : Set E} (hΩ : IsOpen Ω)
    (B : physicalH01Submodule Ω hΩ →L[ℝ] physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ u, ‖u‖ ^ 2 ≤ C * B u u)
    (hsymm : ∀ u v, B u v = B v u) :
    ∃! u, IsPhysicalQuadraticMinimizer hΩ B F (physicalNonnegativeH01Cone Ω hΩ) u := by
  exact @existsUnique_coerciveQuadraticEnergy_minimizer (physicalH01Submodule (d := d) Ω hΩ)
    inferInstance (physicalH01RealNormedSpace (d := d) hΩ) inferInstance B F C hC hbound hsymm
    (physicalNonnegativeH01Cone Ω hΩ) ⟨0, zero_mem_physicalNonnegativeH01Cone hΩ⟩
    (isClosed_physicalNonnegativeH01Cone Ω hΩ) (convex_physicalNonnegativeH01Cone Ω hΩ)

/-- Construct all actual physical Bernstein minima and their strong H01 and
energy convergence for an arbitrary symmetric continuous coercive bilinear
form. The coercivity input is Mathlib's standard IsCoercive property; all
feasible-set closedness, existence and mesh recovery are proved internally.
Concrete mesh-family construction, assembled DOFs and sharp rates remain
outside this theorem. -/
theorem exists_convergent_physicalBernsteinQuadraticMinimizers_of_inscribed_balls
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
    (hball : ∀ m T, Metric.closedBall (c m T) (r m T) ⊆ Set.range (physicalSimplexPoint (b m T)))
    (σ : ℝ) (hσ : 0 ≤ σ) (hshape : ∀ m T, h m T / r m T ≤ σ)
    (B : physicalH01Submodule Ω hΩ →L[ℝ] physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (F : physicalH01Submodule Ω hΩ →L[ℝ] ℝ)
    (hsymm : ∀ u v, B u v = B v u)
    (hcoercive : @IsCoercive (physicalH01Submodule (d := d) Ω hΩ) inferInstance
      (physicalH01RealNormedSpace (d := d) hΩ) B) :
    ∃ (u : physicalH01Submodule Ω hΩ) (uh : ℕ → physicalH01Submodule Ω hΩ),
      IsPhysicalQuadraticMinimizer hΩ B F (physicalNonnegativeH01Cone Ω hΩ) u ∧
      (∀ m, IsPhysicalQuadraticMinimizer hΩ B F (physicalBernsteinH01Cone (b m) n Ω hΩ) (uh m)) ∧
      Tendsto uh atTop (𝓝 u) ∧
      Tendsto (fun m => physicalQuadraticEnergy hΩ B F (uh m)) atTop
        (𝓝 (physicalQuadraticEnergy hΩ B F u)) := by
  obtain ⟨C, hC, hbound⟩ := @inverse_bound_of_coercive_bilin
    (physicalH01Submodule (d := d) Ω hΩ) inferInstance
    (physicalH01RealNormedSpace (d := d) hΩ) B hcoercive
  obtain ⟨u, hu, _⟩ := existsUnique_physicalNonnegativeQuadraticMinimizer hΩ B F C hC hbound hsymm
  have hex (m : ℕ) : ∃ v, IsPhysicalQuadraticMinimizer hΩ B F
      (physicalBernsteinH01Cone (b m) n Ω hΩ) v :=
    (existsUnique_physicalBernsteinQuadraticMinimizer (b m) n hΩ B F C hC hbound hsymm).exists
  choose uh huh using hex
  have hM := mosco_physicalBernsteinH01Cone_of_inscribed_balls b hb hboundary S hsets hΩ hΩS
    n hn H hsmall h hdiam hmax c r hr hball σ hσ hshape
  obtain ⟨v, hv, hvconv⟩ := hM.recovery u hu.1
  have hinner (m : ℕ) : physicalBernsteinH01Cone (b m) n Ω hΩ ⊆
      physicalNonnegativeH01Cone Ω hΩ := by
    apply physicalBernsteinH01Cone_subset_nonnegative (b m) n hΩ
    simpa only [hsets m] using hΩS.trans interior_subset
  have hconv := @tendsto_coerciveQuadraticMinimizers_of_inner_recovery
    (physicalH01Submodule (d := d) Ω hΩ) inferInstance
    (physicalH01RealNormedSpace (d := d) hΩ) B F C hC hbound hsymm
    (physicalNonnegativeH01Cone Ω hΩ) (fun m => physicalBernsteinH01Cone (b m) n Ω hΩ)
    (convex_physicalNonnegativeH01Cone Ω hΩ) hinner u uh v hu huh hv hvconv
  have henergy := @continuous_quadratic_bilin_energy
    (physicalH01Submodule (d := d) Ω hΩ) inferInstance
    (physicalH01RealNormedSpace (d := d) hΩ) B F
  exact ⟨u, uh, hu, huh, hconv, henergy.tendsto u |>.comp hconv⟩

end

end BernsteinObstacle
