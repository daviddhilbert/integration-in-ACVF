module

public import Integration7.HKZeroCoefficientExtensions
public import Integration7.OrdinaryVolumeFamilyScalarProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A weighted zero coefficient acts by an actual finite RV factor.
The family product multiplies its two supplied RV forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}

def ZeroVFVolumeFamily.prodZero (F : ZeroVFVolumeFamily C n a)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    ZeroVFVolumeFamily C n (a+Z.underlying.obj.arity) where
  domain := mixedRVFactorDomain F.domain Z.underlying.obj.domain
  finite_labels := (F.toOrdinary.prodZero Z.underlying).finite_labels
  form := (F.form.prod Z.form).pullback (mixedRVFactorUnpack F.domain Z.underlying.obj.domain)

def zeroVolumeCoefficientInContext (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (x : Fin n → VFType (M := M)) :
    ZeroRVVolumeObject (M := M) ((vfParameterVolumeContext C x).base : Set M) :=
  Z.extend (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h))

def zeroVolumeFamilyScalarRowIso (F : ZeroVFVolumeFamily C n a)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (x : Fin n → VFType (M := M)) :
    ZeroRVVolumeIso ((F.prodZero Z).rowInContext x)
      (product _ 0 0 (F.rowInContext x) (zeroVolumeCoefficientInContext Z x)) := by
  let e := ordinaryVolumeFamilyScalarRowIso F.toOrdinary Z.underlying x
  refine ⟨e,?_⟩
  intro r
  let q := mixedRVFactorUnpack F.domain Z.underlying.obj.domain
    (⟨(x,r.val),r.property⟩ : (F.prodZero Z).domain)
  let t := rvUnpack (F.rowInContext x).underlying.obj.domain
    (zeroVolumeCoefficientInContext Z x).underlying.obj.domain (finiteIsoMap e r)
  have hq := mixed_rv_factor_unpack_value F.domain Z.underlying.obj.domain
    (⟨(x,r.val),r.property⟩ : (F.prodZero Z).domain)
  have ht := congrArg Subtype.val (rvPack_unpack (F.rowInContext x).underlying.obj.domain
    (zeroVolumeCoefficientInContext Z x).underlying.obj.domain (finiteIsoMap e r))
  change Fin.append t.val.1 t.val.2 = r.val at ht
  have ht₁ : t.val.1 = r.val ∘ Fin.castAdd Z.underlying.obj.arity := by
    funext i
    exact (Fin.append_left (m := a) (n := Z.underlying.obj.arity) t.val.1 t.val.2 i).symm.trans
      (congrFun ht (Fin.castAdd Z.underlying.obj.arity i))
  have ht₂ : t.val.2 = r.val ∘ Fin.natAdd a := by
    funext i
    exact (Fin.append_right (m := a) (n := Z.underlying.obj.arity) t.val.1 t.val.2 i).symm.trans
      (congrFun ht (Fin.natAdd a i))
  change F.form.value (Map.prodFst _ _ q) * Z.form.value (Map.prodSnd _ _ q) =
    (F.rowInContext x).form.value (Map.prodFst _ _ t) *
      (zeroVolumeCoefficientInContext Z x).form.value (Map.prodSnd _ _ t)
  congr 1
  · change F.form.value (Map.prodFst _ _ q) = F.form.value ⟨(x,t.val.1),t.property.1⟩
    congr 1
    apply Subtype.ext
    exact (congrArg Prod.fst hq).trans (congrArg (fun z => (x,z)) ht₁).symm
  · change Z.form.value (Map.prodSnd _ _ q) = Z.form.value ⟨t.val.2,t.property.2⟩
    congr 1
    apply Subtype.ext
    exact (congrArg Prod.snd hq).trans ht₂.symm

theorem zero_volume_family_scalar_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C n a) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (x : Fin n → VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) ((F.prodZero Z).rowInContext x) =
      zeroVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
        (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)) (rvVolumeBlowupClass hc C (n := 0) Z) *
          rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) := by
  rw [mul_comm]
  exact Quotient.sound ⟨zeroVolumeFamilyScalarRowIso F Z x⟩

end IntegrationInACVF.Section7.HK
