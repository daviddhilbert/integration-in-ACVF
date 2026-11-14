import Integration7.GradedVolumeProducts
import Integration7.VolumeProductPointwise
import Section4.RVReindexing

/-! Products with ordinary RV[0] retain exactly the positive factor's
coordinates and density. No density is assigned to a degree-zero object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveRVVolumeObject.prod_zero (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) : PositiveRVVolumeObject (M := M) S k where
  underlying := rvFiniteProductObject (k := k+1) (l := 0) U.underlying Z
  form := U.form.pullback ((Map.prodFst U.underlying.obj.domain Z.obj.domain).comp
    (rvUnpack U.underlying.obj.domain Z.obj.domain))

def PositiveRVVolumeObject.zero_prod (Z : RVFiniteObject (M := M) S 0)
    (U : PositiveRVVolumeObject (M := M) S k) : PositiveRVVolumeObject (M := M) S k where
  underlying := ⟨(rvProductObject Z.obj U.underlying.obj).reindexVolume
    (finCongr (Nat.zero_add (k+1)).symm),
    (Map.finiteFibres_of_injective (rvReindexMap_bijective S
      (finCongr (Nat.zero_add (k+1)).symm)).1).comp
      (rvProductObject_finite_volume Z.obj U.underlying.obj Z.property U.underlying.property)⟩
  form := U.form.pullback ((Map.prodSnd Z.obj.domain U.underlying.obj.domain).comp
    (rvUnpack Z.obj.domain U.underlying.obj.domain))

set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.prod_zero PositiveRVVolumeObject.zero_prod
  rvFiniteProductObject Map.prodFst Map.prodSnd

theorem positiveZeroProduct_coordinates (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) (x : (U.prod_zero Z).underlying.obj.domain) :
    (U.prod_zero Z).underlying.obj.value x = U.underlying.obj.value
      (Map.prodFst _ _ (rvUnpack U.underlying.obj.domain Z.obj.domain x)) := by
  change (rvProductObject U.underlying.obj Z.obj).value x = _
  rw [rvProductObject_value]
  have hZ : Z.obj.value (Map.prodSnd _ _ (rvUnpack U.underlying.obj.domain Z.obj.domain x)) =
      Fin.elim0 := funext (fun i => i.elim0)
  have h := congrArg (rvAppend (U.underlying.obj.value
    (Map.prodFst _ _ (rvUnpack U.underlying.obj.domain Z.obj.domain x)))) hZ
  exact h.trans (by simp only [rvAppend,Fin.append_elim0,Fin.cast_refl,Function.comp_id])

theorem zeroPositiveProduct_coordinates (Z : RVFiniteObject (M := M) S 0)
    (U : PositiveRVVolumeObject (M := M) S k) (x : (PositiveRVVolumeObject.zero_prod Z U).underlying.obj.domain) :
    (PositiveRVVolumeObject.zero_prod Z U).underlying.obj.value x = U.underlying.obj.value
      (Map.prodSnd _ _ (rvUnpack Z.obj.domain U.underlying.obj.domain x)) := by
  change (rvProductObject Z.obj U.underlying.obj).value x ∘ finCongr (Nat.zero_add (k+1)).symm = _
  rw [rvProductObject_value]
  have hZ : Z.obj.value (Map.prodFst _ _ (rvUnpack Z.obj.domain U.underlying.obj.domain x)) =
      Fin.elim0 := funext (fun i => i.elim0)
  have h := congrArg (fun t => rvAppend t (U.underlying.obj.value
    (Map.prodSnd _ _ (rvUnpack Z.obj.domain U.underlying.obj.domain x))) ∘
      finCongr (Nat.zero_add (k+1)).symm) hZ
  apply h.trans
  simp only [rvAppend,Fin.elim0_append]
  funext i
  exact congrArg (U.underlying.obj.value
    (Map.prodSnd _ _ (rvUnpack Z.obj.domain U.underlying.obj.domain x))) (Fin.ext rfl)

@[simp] theorem positiveZeroProduct_density (U : PositiveRVVolumeObject (M := M) S k)
    (Z : RVFiniteObject (M := M) S 0) (x : (U.prod_zero Z).underlying.obj.domain) :
    (U.prod_zero Z).form.value x = U.form.value
      (Map.prodFst _ _ (rvUnpack U.underlying.obj.domain Z.obj.domain x)) := rfl

@[simp] theorem zeroPositiveProduct_density (Z : RVFiniteObject (M := M) S 0)
    (U : PositiveRVVolumeObject (M := M) S k) (x : (PositiveRVVolumeObject.zero_prod Z U).underlying.obj.domain) :
    (PositiveRVVolumeObject.zero_prod Z U).form.value x = U.form.value
      (Map.prodSnd _ _ (rvUnpack Z.obj.domain U.underlying.obj.domain x)) := rfl

end IntegrationInACVF.Section7
