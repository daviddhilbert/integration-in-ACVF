module

public import Integration7.HKZeroFamilyScalarProducts
public import Integration7.HKZeroFamilyHeadIntegrals
public import Integration7.VFVolumeBijections
public import Section4.UnionMapLaws

@[expose] public section

/-! Exact finite-factor product bijections for weighted families. The
VF tuple is fixed and the density from each factor is preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ} {C : BaseContext M}

def ZeroVFVolumeFamily.densityGraph (F : ZeroVFVolumeFamily C (n+1) a) :
    ZeroVFVolumeFamily C (n+1) (a+1) where
  domain := F.fullVFObject.densityGraph.domain
  finite_labels := F.fullVFObject.densityGraph.finite_labels
  form := F.fullVFObject.densityGraph.form

set_option maxHeartbeats 1600000 in
def zeroFamilyFiniteProductBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (Z T : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (g : Map F.domain G.domain) (hg : Function.Bijective g)
    (hVF : ∀ p, (g p).val.1=p.val.1)
    (hρ : ∀ p, G.form.value (g p)=F.form.value p) (e : ZeroRVVolumeIso Z T) :
    VFVolumeBijection (F.prodZero Z).fullVFObject (G.prodZero T).fullVFObject := by
  let R := Z.underlying.obj.domain
  let V := T.underlying.obj.domain
  let z := finiteIsoMap e.iso
  have hz : Function.Bijective z := finiteIsoMap_bijective e.iso
  have hUnpack : Function.Bijective (mixedRVFactorUnpack F.domain R) := by
    constructor
    · exact Map.inverse_injective _ (mixed_rv_factor_pack_to_image_bijective F.domain R)
    · intro p
      exact ⟨(mixedRVFactorPack F.domain R).toImage p,mixed_rv_factor_unpack_pack F.domain R p⟩
  let f := (mixedRVFactorPack G.domain V).toImage.comp
    ((Map.prodMap g z).comp (mixedRVFactorUnpack F.domain R))
  have hf : Function.Bijective f := (mixed_rv_factor_pack_to_image_bijective G.domain V).comp
    ((Map.prodMap_bijective g z hg hz).comp hUnpack)
  apply VFVolumeBijection.of_preserving_vf_and_density hc C f hf
  · intro p
    change (g (Map.prodFst _ _ (mixedRVFactorUnpack F.domain R p))).val.1=p.val.1
    rw [hVF]
    exact congrArg (fun v => v.1.1) (mixed_rv_factor_unpack_value F.domain R p)
  · intro p
    symm
    let q := mixedRVFactorUnpack F.domain R p
    let w : DefSet.prod G.domain V := (Map.prodMap g z) q
    change (G.form.prod T.form).value (mixedRVFactorUnpack G.domain V
      ((mixedRVFactorPack G.domain V).toImage w)) = (F.form.prod Z.form).value q
    rw [mixed_rv_factor_unpack_pack]
    change G.form.value (g (Map.prodFst _ _ (mixedRVFactorUnpack F.domain R p))) *
      T.form.value (z (Map.prodSnd _ _ (mixedRVFactorUnpack F.domain R p))) = _
    rw [hρ,← e.density]
    rfl

def zeroFamilyDensityGraphProductBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : ZeroVFVolumeFamily C (n+1) a) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    VFVolumeBijection (F.densityGraph.prodZero Z).fullVFObject (F.prodZero Z).fullVFObject := by
  let g := densityGraphProjection F.fullVFObject.form
  have hg : Function.Bijective g := by
    constructor
    · exact Map.inverse_injective _ (appendDensityMap_toImage_bijective F.fullVFObject.form)
    · intro p
      exact ⟨(appendDensityMap F.fullVFObject.form).toImage p,Map.inverse_apply _ _ p⟩
  exact zeroFamilyFiniteProductBijection hc C F.densityGraph F Z Z g hg
    (fun p => congrArg Prod.fst (densityGraphProjection_value F.fullVFObject.form p))
    (fun _ => rfl) (ZeroRVVolumeIso.refl Z)

end IntegrationInACVF.Section7.HK
