import Integration7.VolumeFamilyPositiveCoefficientData

/-! Finiteness of the genuine positive-coefficient product holds after
fixing the VF base and the full coefficient-first volume tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}

def DefinableVFVolumeFamily.mulConstant (F : DefinableVFVolumeFamily C n a k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    DefinableVFVolumeFamily C n (a+U.underlying.obj.arity) ((p+1)+k) where
  domain := mixedRVFactorDomain F.domain U.underlying.obj.domain
  volume := volumeFamilyConstantVolumeMap F U
  finite_volume x t := by
    let tU : DefSet.univ (rawRVSpace (M := M) (p+1)) (C.base : Set M) :=
      ⟨t ∘ Fin.castAdd (k+1),Set.mem_univ _⟩
    let RU := (U.underlying.property tU).image Subtype.val
    apply (((F.finite_volume x (t ∘ Fin.natAdd (p+1))).prod RU).image
      (fun z => Fin.append z.1 z.2)).subset
    rintro r ⟨q,hq,hv⟩
    let f := volumeFamilyConstantBaseProjection F U q
    let u := volumeFamilyConstantCoefficientProjection F U q
    have hPoints := mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain q
    rw [hq] at hPoints
    change (f.val,u.val) = ((x,r ∘ Fin.castAdd U.underlying.obj.arity),r ∘ Fin.natAdd a) at hPoints
    have hf := congrArg Prod.fst hPoints
    have hu := congrArg Prod.snd hPoints
    change Fin.append (m := p+1) (n := k+1) (U.underlying.obj.value u) (F.volume f).val = t at hv
    have hvU : U.underlying.obj.volume u=tU := by
      apply Subtype.ext
      funext i
      change U.underlying.obj.value u i = t (Fin.castAdd (k+1) i)
      simpa only [Fin.append_left,Function.comp_apply] using congrFun hv (Fin.castAdd (k+1) i)
    have hvF : (F.volume f).val=t ∘ Fin.natAdd (p+1) := by
      funext i
      simpa only [Fin.append_right,Function.comp_apply] using congrFun hv (Fin.natAdd (p+1) i)
    refine ⟨(r ∘ Fin.castAdd U.underlying.obj.arity,r ∘ Fin.natAdd a),⟨?_,?_⟩,Fin.append_castAdd_natAdd⟩
    · exact ⟨f,hf,hvF⟩
    · exact ⟨u,hvU,hu⟩
  form := volumeFamilyConstantForm F U

end IntegrationInACVF.Section7
