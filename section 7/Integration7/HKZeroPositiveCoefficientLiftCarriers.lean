import Integration7.HKZeroFamilyPositiveCoefficients
import Integration7.DefinableAppendedLiftCarriers
import Integration7.MixedProductCoordinateFormulas
import Integration7.PositiveVFVolumeProducts

/-! Literal carrier comparison for the coefficient-first realization
of a positive coefficient multiplying an ordinary family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

theorem zero_positive_coefficient_lift_degree (n p : ℕ) : appendVolumeDegree (n+1) p=(p+1)+n := by
  rw [append_volume_degree_eq]
  omega

def zeroPositiveCoefficientVFProduct (F : ZeroVFVolumeFamily C (n+1) a)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) (appendVolumeDegree (n+1) p) :=
  ((rvVolumeLift U).prod F.fullVFObject).reindexDegree (zero_positive_coefficient_lift_degree n p)

theorem zero_positive_coefficient_lift_carrier
    (F : ZeroVFVolumeFamily C (n+1) a)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin (appendVolumeDegree (n+1) p+1) → VFType (M := M))
    (r : Fin a → CanonicalRV.RVSort M) (s : Fin U.underlying.obj.arity → CanonicalRV.RVSort M) :
    (x,Fin.append r s) ∈ (F.mulConstant U).appendedFullLift.domain.carrier ↔
      (x,Fin.append s r) ∈ (zeroPositiveCoefficientVFProduct F U).domain.carrier := by
  let h := zero_positive_coefficient_lift_degree n p
  let y := x ∘ (finCongr (congrArg Nat.succ h)).symm
  have hHead : y ∘ Fin.castAdd (n+1)=appendedFamilyCoefficientCoordinates (n+1) p x := by
    funext i
    apply congrArg x
    exact Fin.ext rfl
  have hTail : y ∘ Fin.natAdd (p+1)=appendedFamilyBaseCoordinates (n+1) p x := by
    funext i
    apply congrArg x
    exact Fin.ext rfl
  rw [mem_definable_appended_family_lift]
  change _ ↔ (x,Fin.append s r) ∈
    (((rvVolumeLift U).prod F.fullVFObject).reindexDegree h).domain.carrier
  rw [mem_vf_volume_reindex_degree]
  change _ ↔ (y,Fin.append s r) ∈
    (mixedProductDomain (n := p+1) (m := n+1) (rvVolumeLift U).domain F.domain).carrier
  rw [mem_mixedProductDomain]
  change _ ↔ (y ∘ Fin.castAdd (n+1),Fin.append s r ∘ Fin.castAdd a) ∈ (rvVolumeLift U).domain.carrier ∧
    (y ∘ Fin.natAdd (p+1),Fin.append s r ∘ Fin.natAdd U.underlying.obj.arity) ∈ F.domain.carrier
  simp only [Function.comp_def,Fin.append_left,Fin.append_right]
  change _ ↔ (y ∘ Fin.castAdd (n+1),s) ∈ (rvVolumeLift U).domain.carrier ∧
    (y ∘ Fin.natAdd (p+1),r) ∈ F.domain.carrier
  rw [hHead,hTail]
  constructor
  · rintro ⟨q,hq,hv⟩
    let u := ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U q
    have hp := mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain q
    rw [hq] at hp
    simp only [Function.comp_def,Fin.append_left,Fin.append_right] at hp
    have hf := congrArg Prod.fst hp
    have hu := congrArg Prod.snd hp
    have hs : u.val=s := by
      exact hu
    have hr : (appendedFamilyBaseCoordinates (n+1) p x,r) ∈ F.domain.carrier := by
      have hfmem := (mixedRVFactorUnpack F.domain U.underlying.obj.domain q).property.1
      exact Eq.mp (congrArg (fun z => z ∈ F.domain.carrier) hf) hfmem
    refine ⟨⟨⟨s,hs ▸ u.property⟩,rfl,?_⟩,hr⟩
    have hvol : tupleRV (appendedFamilyCoefficientCoordinates (n+1) p x)=U.underlying.obj.value u := hv
    have he : (⟨s,hs ▸ u.property⟩ : U.underlying.obj.domain)=u := Subtype.ext hs.symm
    exact (congrArg U.underlying.obj.value he).trans hvol.symm
  · rintro ⟨⟨u,hu,hv⟩,hr⟩
    let q : (F.mulConstant U).domain :=
      (mixedRVFactorPack F.domain U.underlying.obj.domain).toImage
        ⟨((appendedFamilyBaseCoordinates (n+1) p x,r),u.val),hr,u.property⟩
    refine ⟨q,?_,?_⟩
    · change (appendedFamilyBaseCoordinates (n+1) p x,Fin.append r u.val)=_
      exact Prod.ext rfl (congrArg (Fin.append r) hu)
    · change tupleRV (appendedFamilyCoefficientCoordinates (n+1) p x)=
        U.underlying.obj.value (Map.prodSnd _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain
          ((mixedRVFactorPack F.domain U.underlying.obj.domain).toImage
            ⟨((appendedFamilyBaseCoordinates (n+1) p x,r),u.val),hr,u.property⟩)))
      rw [mixed_rv_factor_unpack_pack]
      exact hv.symm

end IntegrationInACVF.Section7.HK
