import BernsteinObstacle.SimplexSamplingFaceRestriction
import BernsteinObstacle.PhysicalSimplexCoordinates

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem physicalSimplexPoint_permutedPoint {d : ℕ} (v : Fin (d + 1) → E)
    (e : Fin (d + 1) ≃ Fin (d + 1)) (x : BarycentricPoint d) :
    physicalSimplexPoint v (permuteBarycentricPoint d e x) =
      physicalSimplexPoint (fun i => v (e.symm i)) x := by
  unfold physicalSimplexPoint
  change (∑ i, x.1 (e i) • v i) = ∑ i, x.1 i • v (e.symm i)
  simpa using e.sum_comp (fun i => x.1 i • v (e.symm i))

theorem physicalSimplexPoint_lastFace {d : ℕ} (v : Fin (d + 2) → E)
    (x : BarycentricPoint d) :
    physicalSimplexPoint v (lastFacePoint d x) =
      physicalSimplexPoint (fun i => v i.castSucc) x := by
  unfold physicalSimplexPoint
  rw [Fin.sum_univ_castSucc]
  simp

theorem physicalSimplexPoint_orientedLastFace {d : ℕ} (v : Fin (d + 2) → E)
    (e : Fin (d + 2) ≃ Fin (d + 2)) (x : BarycentricPoint d) :
    physicalSimplexPoint v (orientedLastFacePoint d e x) =
      physicalSimplexPoint (fun i => v (e.symm i.castSucc)) x := by
  unfold orientedLastFacePoint
  rw [physicalSimplexPoint_permutedPoint, physicalSimplexPoint_lastFace]

theorem physicalSamplingRecovery_orientedLastFace {d : ℕ}
    (v : Fin (d + 2) → E) (n : ℕ) (hn : 0 < n)
    (e : Fin (d + 2) ≃ Fin (d + 2)) (f : E → ℝ) (x : BarycentricPoint d) :
    physicalSamplingRecovery v n hn f (orientedLastFacePoint d e x) =
      physicalSamplingRecovery (fun i => v (e.symm i.castSucc)) n hn f x := by
  unfold physicalSamplingRecovery
  rw [simplexSamplingRecovery_orientedLastFace]
  simp_rw [physicalSimplexPoint_orientedLastFace]

/-- A face of any codimension, built by successively taking oriented facets.
`refl` includes the whole simplex. No recovery equality is assumed as data. -/
inductive SimplexSubface (k : ℕ) : ℕ → Type
  | refl : SimplexSubface k k
  | step {d : ℕ} (orientation : Fin (d + 2) ≃ Fin (d + 2))
      (face : SimplexSubface k d) : SimplexSubface k (d + 1)

namespace SimplexSubface

def point {k : ℕ} : {d : ℕ} → SimplexSubface k d →
    BarycentricPoint k → BarycentricPoint d
  | _, .refl, x => x
  | _, .step e q, x => orientedLastFacePoint _ e (q.point x)

def vertices {k : ℕ} : {d : ℕ} → SimplexSubface k d →
    (Fin (d + 1) → E) → Fin (k + 1) → E
  | _, .refl, v => v
  | _, .step e q, v => q.vertices (fun i => v (e.symm i.castSucc))

end SimplexSubface

theorem physicalSimplexPoint_subface {k d : ℕ} (q : SimplexSubface k d)
    (v : Fin (d + 1) → E) (x : BarycentricPoint k) :
    physicalSimplexPoint v (q.point x) = physicalSimplexPoint (q.vertices v) x := by
  induction q with
  | refl => rfl
  | step e q ih =>
    change physicalSimplexPoint v (orientedLastFacePoint _ e (q.point x)) = _
    rw [physicalSimplexPoint_orientedLastFace]
    exact ih _

/-- Exact physical sampling restriction on faces of every codimension. -/
theorem physicalSamplingRecovery_subface {k d : ℕ} (q : SimplexSubface k d)
    (v : Fin (d + 1) → E) (n : ℕ) (hn : 0 < n)
    (f : E → ℝ) (x : BarycentricPoint k) :
    physicalSamplingRecovery v n hn f (q.point x) =
      physicalSamplingRecovery (q.vertices v) n hn f x := by
  induction q with
  | refl => rfl
  | step e q ih =>
    change physicalSamplingRecovery v n hn f (orientedLastFacePoint _ e (q.point x)) = _
    rw [physicalSamplingRecovery_orientedLastFace]
    exact ih _

variable [FiniteDimensional ℝ E]

theorem affineBasisPhysicalSamplingRecovery_subface {k d : ℕ}
    (q : SimplexSubface k d) (b : AffineBasis (Fin (d + 1)) ℝ E)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (x : BarycentricPoint k) :
    affineBasisPhysicalSamplingRecovery b n hn f (physicalSimplexPoint b (q.point x)) =
      physicalSamplingRecovery (q.vertices (fun i => b i)) n hn f x := by
  rw [affineBasisPhysicalSamplingRecovery_eq, physicalSamplingRecovery_subface]

/-- Geometric equality of the ordered physical face vertices gives equality
of the actual element polynomials on that common face, not an assumed trace. -/
theorem affineBasisPhysicalSamplingRecovery_sharedSubface {k d : ℕ}
    (bT bU : AffineBasis (Fin (d + 1)) ℝ E)
    (qT qU : SimplexSubface k d)
    (hvertices : qT.vertices (fun i => bT i) = qU.vertices (fun i => bU i))
    (n : ℕ) (hn : 0 < n) (f : E → ℝ) (x : BarycentricPoint k) (p : E)
    (hT : physicalSimplexPoint bT (qT.point x) = p)
    (hU : physicalSimplexPoint bU (qU.point x) = p) :
    affineBasisPhysicalSamplingRecovery bT n hn f p =
      affineBasisPhysicalSamplingRecovery bU n hn f p := by
  calc
    affineBasisPhysicalSamplingRecovery bT n hn f p =
        physicalSamplingRecovery (qT.vertices (fun i => bT i)) n hn f x := by
      rw [← hT]
      exact affineBasisPhysicalSamplingRecovery_subface qT bT n hn f x
    _ = physicalSamplingRecovery (qU.vertices (fun i => bU i)) n hn f x := by
      rw [hvertices]
    _ = affineBasisPhysicalSamplingRecovery bU n hn f p := by
      rw [← hU]
      exact (affineBasisPhysicalSamplingRecovery_subface qU bU n hn f x).symm

/-- Zero data on an actual physical face yields a zero recovered trace there. -/
theorem affineBasisPhysicalSamplingRecovery_zero_subface {k d : ℕ}
    (q : SimplexSubface k d) (b : AffineBasis (Fin (d + 1)) ℝ E)
    (n : ℕ) (hn : 0 < n) (f : E → ℝ)
    (hf : ∀ y : BarycentricPoint k,
      f (physicalSimplexPoint (q.vertices (fun i => b i)) y) = 0)
    (x : BarycentricPoint k) :
    affineBasisPhysicalSamplingRecovery b n hn f (physicalSimplexPoint b (q.point x)) = 0 := by
  rw [affineBasisPhysicalSamplingRecovery_subface]
  unfold physicalSamplingRecovery simplexSamplingRecovery simplexField simplexSamplingCoefficients
  apply Finset.sum_eq_zero
  intro α _
  simp only [hf, zero_mul]

end

end BernsteinObstacle
