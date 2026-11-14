import Integration7.PositiveVolumeParameterExtension
import Integration7.RVAlmostEverywhereParameters

/-! The actual essential isomorphism and both volume equations persist
under enlargement of the real parameter set. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S T : Set M} {n k : ℕ}

def finiteVolumeIsoExtend (hST : S ⊆ T) {U V : RVFiniteObject (M := M) S n}
    (e : U ≅ V) : Section6.FiniteRV.extendObject hST U ≅ Section6.FiniteRV.extendObject hST V :=
  rvFiniteIsoOfAmbient (Section6.extendIso hST ((finiteVolumeProperty S n).ι.mapIso e))

@[simp] theorem finiteVolumeIsoExtend_apply (hST : S ⊆ T)
    {U V : RVFiniteObject (M := M) S n} (e : U ≅ V)
    (u : (Section6.FiniteRV.extendObject hST U).obj.domain) :
    (finiteIsoMap (finiteVolumeIsoExtend hST e) u).val =
      (finiteIsoMap e ⟨u.val,u.property⟩).val := rfl

def RVVolumeIso.extend {U V : PositiveRVVolumeObject (M := M) S k}
    (e : RVVolumeIso U V) (hST : S ⊆ T) : RVVolumeIso (U.extend hST) (V.extend hST) where
  iso := finiteVolumeIsoExtend hST e.iso
  gamma := e.gamma
  rv := e.rv.extend hST

@[simp] theorem RVVolumeIso.extend_apply {U V : PositiveRVVolumeObject (M := M) S k}
    (e : RVVolumeIso U V) (hST : S ⊆ T) (u : (U.extend hST).essential.obj.domain) :
    (finiteIsoMap (e.extend hST).iso u).val = (finiteIsoMap e.iso ⟨u.val,u.property⟩).val := rfl

end IntegrationInACVF.Section7
