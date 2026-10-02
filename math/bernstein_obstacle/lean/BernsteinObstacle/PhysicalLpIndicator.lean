import BernsteinObstacle.PhysicalFiniteLpCone
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal BigOperators

namespace BernsteinObstacle

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The actual L2 class obtained by restricting a representative to a
measurable cell and extending it by zero. -/
def physicalLpIndicator (s : Set α) (hs : MeasurableSet s) (u : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ((Lp.memLp u).indicator hs).toLp (s.indicator u)

theorem physicalLpIndicator_coe (s : Set α) (hs : MeasurableSet s) (u : Lp ℝ 2 μ) :
    physicalLpIndicator s hs u =ᵐ[μ] s.indicator u :=
  ((Lp.memLp u).indicator hs).coeFn_toLp

theorem physicalLpIndicator_add (s : Set α) (hs : MeasurableSet s) (u v : Lp ℝ 2 μ) :
    physicalLpIndicator s hs (u + v) = physicalLpIndicator s hs u + physicalLpIndicator s hs v := by
  apply Lp.ext
  filter_upwards [physicalLpIndicator_coe s hs (u + v),
    Lp.coeFn_add (physicalLpIndicator s hs u) (physicalLpIndicator s hs v),
    physicalLpIndicator_coe s hs u, physicalLpIndicator_coe s hs v, Lp.coeFn_add u v]
    with x hleft hright hu hv hadd
  rw [hleft, hright, Pi.add_apply, hu, hv]
  by_cases hx : x ∈ s
  · simpa only [Set.indicator_of_mem hx, Pi.add_apply] using hadd
  · simp [hx]

theorem physicalLpIndicator_smul (s : Set α) (hs : MeasurableSet s) (r : ℝ) (u : Lp ℝ 2 μ) :
    physicalLpIndicator s hs (r • u) = r • physicalLpIndicator s hs u := by
  apply Lp.ext
  filter_upwards [physicalLpIndicator_coe s hs (r • u),
    Lp.coeFn_smul r (physicalLpIndicator s hs u), physicalLpIndicator_coe s hs u,
    Lp.coeFn_smul r u] with x hleft hright hu hsmul
  rw [hleft, hright, Pi.smul_apply, hu]
  by_cases hx : x ∈ s <;> simp [hx, hsmul, Pi.smul_apply]

theorem physicalLpIndicator_norm_le (s : Set α) (hs : MeasurableSet s) (u : Lp ℝ 2 μ) :
    ‖physicalLpIndicator s hs u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [physicalLpIndicator_coe s hs u] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- A proved continuous linear cell-indicator map, with actual norm bound
one. No restriction-operator or representative-choice oracle is supplied. -/
def physicalLpIndicatorCLM (s : Set α) (hs : MeasurableSet s) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ({ toFun := physicalLpIndicator s hs
     map_add' := physicalLpIndicator_add s hs
     map_smul' := physicalLpIndicator_smul s hs } : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).mkContinuous
    1 (fun u => by
      change ‖physicalLpIndicator s hs u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using physicalLpIndicator_norm_le s hs u)

theorem physicalLpIndicatorCLM_apply (s : Set α) (hs : MeasurableSet s) (u : Lp ℝ 2 μ) :
    physicalLpIndicatorCLM s hs u = physicalLpIndicator s hs u := rfl

end

end BernsteinObstacle
