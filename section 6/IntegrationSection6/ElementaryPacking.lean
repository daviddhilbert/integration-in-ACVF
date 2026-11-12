import IntegrationSection6.ElementaryBlowup
import Section4.RVProductAssociativity

/-! Projection and parameter of the actual packed elementary domain. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

/-- The elementary parameter is the last packed domain coordinate. -/
@[simp] theorem elementaryProjection_pair (U : RVObject (M := M) S k) (i : Fin k)
    (u : U.domain) (s : positiveRV (M := M) S) :
    elementaryProjection U i (rvPackPair U.domain (positiveRV S) u s) = u := by
  change (Map.prodFst U.domain (positiveRV S))
    (rvUnpack U.domain (positiveRV S) (rvPackPair U.domain (positiveRV S) u s)) = u
  rw [rvUnpack_pair]
  rfl

@[simp] theorem elementaryParameter_pair (U : RVObject (M := M) S k) (i : Fin k)
    (u : U.domain) (s : positiveRV (M := M) S) :
    elementaryParameter U i (rvPackPair U.domain (positiveRV S) u s) = s := by
  change (Map.prodSnd U.domain (positiveRV S))
    (rvUnpack U.domain (positiveRV S) (rvPackPair U.domain (positiveRV S) u s)) = s
  rw [rvUnpack_pair]
  rfl

end IntegrationInACVF.Section6
