import BernsteinObstacle.BoundedMollification
import BernsteinObstacle.LipschitzWeakDerivative

open MeasureTheory Set Function Filter ContinuousLinearMap Topology
open scoped ENNReal Convolution

namespace BernsteinObstacle

noncomputable section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-!
The reflected-test-function integration-by-parts argument and the passage
through the convolution derivative adapt DeGiorgi/SobolevSpace/Approximation.lean,
commit 4c1b3077d3782b24065184df4ba59501b2e56fc7 (Apache-2.0), onto this project's
actual weak-derivative predicate and current pinned Mathlib stack.
-/

theorem convolution_fderiv_eq_convolution_weakPartial
    {u g φ : E → ℝ} {i : Fin d}
    (hweak : SobolevH01Port.HasWeakPartialDeriv i g u Set.univ)
    (hφ : ContDiff ℝ (⊤ : ENat) φ) (hcompact : HasCompactSupport φ) (x : E) :
    ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
      ⋆[lsmul ℝ ℝ, volume] u) x = (φ ⋆[lsmul ℝ ℝ, volume] g) x := by
  let T : Homeomorph E E := (Homeomorph.neg E).trans (Homeomorph.addLeft x)
  let ψ : E → ℝ := φ ∘ T
  have hψ : ContDiff ℝ (⊤ : ENat) ψ := by
    simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
      hφ.comp (contDiff_const.add contDiff_id.neg)
  have hψc : HasCompactSupport ψ := by
    simpa [ψ, T, Function.comp] using hcompact.comp_homeomorph T
  have key := hweak ψ hψ hψc (by simp)
  have hderiv : ∀ t,
      (fderiv ℝ ψ t) (EuclideanSpace.single i 1) =
        -(fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) := by
    intro t
    have hfd : HasFDerivAt ψ
        ((fderiv ℝ φ (x + -t)).comp ((0 : E →L[ℝ] E) - 1)) t := by
      simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
        ((hφ.differentiable (by simp) (x + -t)).hasFDerivAt.comp t
          ((hasFDerivAt_const x t).add (hasFDerivAt_id t).neg))
    rw [hfd.fderiv]
    simp
  have hkey : ∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) =
      ∫ t, g t * ψ t := by
    simpa only [Measure.restrict_univ, hderiv, mul_neg, integral_neg, neg_inj] using key
  calc
    ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
      ⋆[lsmul ℝ ℝ, volume] u) x =
        ∫ t, u t * (fderiv ℝ φ (x - t)) (EuclideanSpace.single i 1) := by
          simpa [smul_eq_mul, mul_comm] using
            (convolution_lsmul_swap
              (f := fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
              (g := u) (x := x) (μ := volume))
    _ = ∫ t, g t * ψ t := hkey
    _ = (φ ⋆[lsmul ℝ ℝ, volume] g) x := by
      simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc, smul_eq_mul, mul_comm] using
        (convolution_lsmul_swap (f := φ) (g := g) (x := x) (μ := volume)).symm

/-- Differentiating the actual mollification gives convolution with the
actual weak derivative, not an independently chosen approximation. -/
theorem fderiv_convolution_apply_eq_convolution_weakPartial
    {u g φ : E → ℝ} {i : Fin d}
    (hu : LocallyIntegrable u volume)
    (hweak : SobolevH01Port.HasWeakPartialDeriv i g u Set.univ)
    (hφ : ContDiff ℝ (⊤ : ENat) φ) (hcompact : HasCompactSupport φ) (x : E) :
    (fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] u) x) (EuclideanSpace.single i 1) =
      (φ ⋆[lsmul ℝ ℝ, volume] g) x := by
  let Dφ := fderiv ℝ φ
  let ei : E := EuclideanSpace.single i 1
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hfd := hcompact.hasFDerivAt_convolution_left (L := lsmul ℝ ℝ) hφ1 hu x
  have hDφc : HasCompactSupport Dφ := hcompact.fderiv (𝕜 := ℝ)
  have hDφcont : Continuous Dφ := hφ1.continuous_fderiv one_ne_zero
  have hconv : ((Dφ ⋆[(lsmul ℝ ℝ).precompL E, volume] u) x) ei =
      ((fun y => Dφ y ei) ⋆[lsmul ℝ ℝ, volume] u) x := by
    calc
      ((Dφ ⋆[(lsmul ℝ ℝ).precompL E, volume] u) x) ei =
          ((u ⋆[(lsmul ℝ ℝ).flip.precompR E, volume] Dφ) x) ei := by
        simpa [ContinuousLinearMap.precompL, Dφ] using
          congrArg (fun F => F x ei)
            (convolution_flip (L := (lsmul ℝ ℝ).flip.precompR E)
              (μ := volume) (f := u) (g := Dφ))
      _ = (u ⋆[(lsmul ℝ ℝ).flip, volume] (fun y => Dφ y ei)) x :=
        convolution_precompR_apply (lsmul ℝ ℝ).flip hu hDφc hDφcont x ei
      _ = ((fun y => Dφ y ei) ⋆[lsmul ℝ ℝ, volume] u) x := by
        simpa using congrArg (fun F => F x)
          (convolution_flip (L := lsmul ℝ ℝ) (μ := volume)
            (f := fun y => Dφ y ei) (g := u))
  calc
    (fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] u) x) ei =
        ((Dφ ⋆[(lsmul ℝ ℝ).precompL E, volume] u) x) ei := by
      exact congrArg (fun A : E →L[ℝ] ℝ => A ei) hfd.fderiv
    _ = ((fun y => Dφ y ei) ⋆[lsmul ℝ ℝ, volume] u) x := hconv
    _ = (φ ⋆[lsmul ℝ ℝ, volume] g) x :=
      convolution_fderiv_eq_convolution_weakPartial hweak hφ hcompact x

theorem fderiv_physicalMollification_apply (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    {f : E → ℝ} {C : NNReal} (hf : LipschitzWith C f) (hc : HasCompactSupport f)
    (i : Fin d) (x : E) :
    (fderiv ℝ (physicalMollification δ hδ n f) x) (EuclideanSpace.single i 1) =
      physicalMollification δ hδ n
        (fun y => (fderiv ℝ f y) (EuclideanSpace.single i 1)) x := by
  apply fderiv_convolution_apply_eq_convolution_weakPartial hf.continuous.locallyIntegrable
    (hasWeakPartialDeriv_of_lipschitz_hasCompactSupport hf hc isOpen_univ i)
    (physicalShrinkingBump δ hδ n).contDiff_normed
    (physicalShrinkingBump δ hδ n).hasCompactSupport_normed x

end

end BernsteinObstacle
