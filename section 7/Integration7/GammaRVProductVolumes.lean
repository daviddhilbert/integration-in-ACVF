module

public import Integration7.GammaRVProductMaps

@[expose] public section

/-! The complete volume graph of an actual RV product is obtained
from the two factor volume graphs over the same original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {k l : ℕ}

private def coordinateRVObject (S : Set M) (n : ℕ) : RVObject (M := M) S n :=
  ⟨n,DefSet.univ (rawRVSpace n) S,Map.id _⟩

theorem RVMapGamma.product_volume {U : RVObject (M := M) S k} {V : RVObject (M := M) S l}
    (hU : RVMapGamma U.volume P) (hV : RVMapGamma V.volume P) :
    RVMapGamma (rvProductObject U V).volume P :=
  (hU.prod (U := U) (V := V) (U' := coordinateRVObject S k) (V' := coordinateRVObject S l) hV).congr
    (fun _ => rfl)

end IntegrationInACVF.Section7
