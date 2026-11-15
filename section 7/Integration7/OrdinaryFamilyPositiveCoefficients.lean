import Integration7.OrdinaryVFVolumeFamilies
import Integration7.DefinableVFVolumeFamilies
import Integration7.MixedRVFactorDomains
import Integration7.GradedVolumeProducts

/-! A positive coefficient times an ordinary-valued family retains
only the coefficient's volume tuple and density, on the actual product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

def ordinaryFamilyPositiveCoefficientProjection (F : OrdinaryVFVolumeFamily C n a)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    Map (mixedRVFactorDomain F.domain U.underlying.obj.domain) U.underlying.obj.domain :=
  (Map.prodSnd F.domain U.underlying.obj.domain).comp (mixedRVFactorUnpack F.domain U.underlying.obj.domain)

def OrdinaryVFVolumeFamily.mulConstant (F : OrdinaryVFVolumeFamily C n a)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    DefinableVFVolumeFamily C n (a+U.underlying.obj.arity) p where
  domain := mixedRVFactorDomain F.domain U.underlying.obj.domain
  volume := U.underlying.obj.volume.comp (ordinaryFamilyPositiveCoefficientProjection F U)
  finite_volume x t := by
    let tU : DefSet.univ (rawRVSpace (M := M) (p+1)) (C.base : Set M) := ⟨t,Set.mem_univ _⟩
    apply (((F.finite_labels x).prod ((U.underlying.property tU).image Subtype.val)).image
      (fun q => Fin.append q.1 q.2)).subset
    rintro r ⟨q,hq,hv⟩
    let f := Map.prodFst F.domain U.underlying.obj.domain (mixedRVFactorUnpack F.domain U.underlying.obj.domain q)
    let u := ordinaryFamilyPositiveCoefficientProjection F U q
    have hPoints := mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain q
    rw [hq] at hPoints
    change (f.val,u.val)=((x,r ∘ Fin.castAdd U.underlying.obj.arity),r ∘ Fin.natAdd a) at hPoints
    have hf := congrArg Prod.fst hPoints
    have hu := congrArg Prod.snd hPoints
    have hvol : U.underlying.obj.volume u=tU := Subtype.ext hv
    refine ⟨(r ∘ Fin.castAdd U.underlying.obj.arity,r ∘ Fin.natAdd a),⟨?_,?_⟩,Fin.append_castAdd_natAdd⟩
    · exact Eq.mp (congrArg (fun q => q ∈ F.domain.carrier) hf) f.property
    · exact ⟨u,hvol,hu⟩
  form := U.form.pullback (ordinaryFamilyPositiveCoefficientProjection F U)

@[simp] theorem ordinary_family_positive_coefficient_volume
    (F : OrdinaryVFVolumeFamily C n a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : (F.mulConstant U).domain) :
    ((F.mulConstant U).volume q).val = U.underlying.obj.value (ordinaryFamilyPositiveCoefficientProjection F U q) := rfl

@[simp] theorem ordinary_family_positive_coefficient_density
    (F : OrdinaryVFVolumeFamily C n a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : (F.mulConstant U).domain) :
    (F.mulConstant U).form.value q=U.form.value (ordinaryFamilyPositiveCoefficientProjection F U q) := rfl

end IntegrationInACVF.Section7
