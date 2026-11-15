import Integration7.MixedRVFactorDomains
import Integration7.SelectedVolumeFamilies
import Integration7.ZeroFactorVolumeObjects

/-! Ordinary degree-zero coefficients multiply a positive family by
an actual finite RV factor. The selected volume coordinates and density
come entirely from the positive family, as in the paper's RV[0] convention. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

theorem ordinary_zero_volume_domain_finite {S : Set M} (Z : RVFiniteObject (M := M) S 0) :
    Z.obj.domain.carrier.Finite := by
  apply ((Z.property ⟨Fin.elim0,Set.mem_univ _⟩).image Subtype.val).subset
  intro r hr
  exact ⟨⟨r,hr⟩,Subtype.ext (funext (fun i => i.elim0)),rfl⟩

def SelectedVFVolumeFamily.prodZero (F : SelectedVFVolumeFamily C n a k)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    SelectedVFVolumeFamily C n (a+Z.obj.arity) k where
  domain := mixedRVFactorDomain F.domain Z.obj.domain
  selected := Fin.castAdd Z.obj.arity ∘ F.selected
  finite_selected x t := by
    apply (((F.finite_selected x t).prod (ordinary_zero_volume_domain_finite Z)).image
      (fun q => Fin.append q.1 q.2)).subset
    rintro r ⟨hr,ht⟩
    have h := (mem_mixed_rv_factor_domain F.domain Z.obj.domain x r).mp hr
    refine ⟨(r ∘ Fin.castAdd Z.obj.arity,r ∘ Fin.natAdd a),⟨⟨h.1,?_⟩,h.2⟩,Fin.append_castAdd_natAdd⟩
    exact ht
  form := F.form.pullback ((Map.prodFst F.domain Z.obj.domain).comp
    (mixedRVFactorUnpack F.domain Z.obj.domain))

def SelectedVFVolumeFamily.prodZeroProjection (F : SelectedVFVolumeFamily C n a k)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) : Map (F.prodZero Z).domain F.domain :=
  (Map.prodFst F.domain Z.obj.domain).comp (mixedRVFactorUnpack F.domain Z.obj.domain)

theorem SelectedVFVolumeFamily.prodZeroProjection_value (F : SelectedVFVolumeFamily C n a k)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) (p : (F.prodZero Z).domain) :
    (F.prodZeroProjection Z p).val = (p.val.1,p.val.2 ∘ Fin.castAdd Z.obj.arity) :=
  congrArg Prod.fst (mixed_rv_factor_unpack_value F.domain Z.obj.domain p)

@[simp] theorem SelectedVFVolumeFamily.prodZero_density (F : SelectedVFVolumeFamily C n a k)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) (p : (F.prodZero Z).domain) :
    (F.prodZero Z).form.value p = F.form.value (F.prodZeroProjection Z p) := rfl

end IntegrationInACVF.Section7
