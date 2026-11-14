import Integration7.RVVolumeMorphisms

noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

@[simp] theorem finiteIsoMap_symm_apply {U V : RVFiniteObject (M := M) S n}
    (e : U ≅ V) (u : U.obj.domain) :
    finiteIsoMap e.symm (finiteIsoMap e u) = u :=
  SpecialTransformations.Section4.rvIso_inv_apply ((finiteVolumeProperty S n).ι.mapIso e) u

@[simp] theorem finiteIsoMap_apply_symm {U V : RVFiniteObject (M := M) S n}
    (e : U ≅ V) (v : V.obj.domain) :
    finiteIsoMap e (finiteIsoMap e.symm v) = v :=
  finiteIsoMap_symm_apply e.symm v

theorem finiteIsoMap_injective {U V : RVFiniteObject (M := M) S n} (e : U ≅ V) :
    Function.Injective (finiteIsoMap e) :=
  (show Function.LeftInverse (finiteIsoMap e.symm) (finiteIsoMap e) from
    finiteIsoMap_symm_apply e).injective

theorem finiteIsoMap_bijective {U V : RVFiniteObject (M := M) S n} (e : U ≅ V) :
    Function.Bijective (finiteIsoMap e) :=
  ⟨finiteIsoMap_injective e, fun v => ⟨finiteIsoMap e.symm v, finiteIsoMap_apply_symm e v⟩⟩

@[simp] theorem finiteIsoMap_trans {U V W : RVFiniteObject (M := M) S n}
    (e : U ≅ V) (f : V ≅ W) (u : U.obj.domain) :
    finiteIsoMap (e.trans f) u = finiteIsoMap f (finiteIsoMap e u) := rfl

end IntegrationInACVF.Section7
