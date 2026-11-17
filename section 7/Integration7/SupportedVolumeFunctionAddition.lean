module

public import Integration7.SupportedVolumeFunctionJacobians
public import Integration7.AERVVolumeFunctionAdditiveStructure

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Functions supported on a specified definable domain have the
actual pointwise additive structure inherited through their injective
map into all almost-everywhere functions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_volume_family_sum_supported
    {C : BaseContext M} {X : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (hG : ∀ p : G.domain, p.val.1 ∈ X.carrier) :
    ∀ q : (selectedVolumeFamilySum F G).domain, q.val.1 ∈ X.carrier := by
  rintro ⟨q,p,hp⟩
  have he := congrArg Prod.fst hp
  change p.val.1 = q.1 at he
  rw [← he]
  rcases p.property with ⟨u,hu⟩ | ⟨v,hv⟩
  · have h := congrArg Prod.fst hu
    change u.val.1=p.val.1 at h
    exact h ▸ hF u
  · have h := congrArg Prod.fst hv
    change v.val.1=p.val.1 at h
    exact h ▸ hG v

instance supportedVolumeFunctionAdd
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Add (SupportedAERVVolumeFunction hc C X k) :=
  ⟨Quotient.map₂ (fun F G => ⟨_,⟨selectedVolumeFamilySum F.2.val G.2.val,
      selected_volume_family_sum_supported F.2.val G.2.val F.2.property G.2.property⟩⟩)
    (fun F F' hF G G' hG =>
      ae_selected_volume_family_sum_congr hc C F.2.val F'.2.val G.2.val G'.2.val hF hG)⟩

instance supportedVolumeFunctionZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Zero (SupportedAERVVolumeFunction hc C X k) :=
  ⟨Quotient.mk _ ⟨k+1,⟨selectedZeroVolumeFamily C (n+1) k,fun p => False.elim p.property⟩⟩⟩

theorem supported_volume_function_forget_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (f g : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionForget hc C X (f+g) =
      supportedVolumeFunctionForget hc C X f + supportedVolumeFunctionForget hc C X g :=
  Quotient.inductionOn₂ f g (fun _ _ => rfl)

theorem supported_volume_function_forget_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    supportedVolumeFunctionForget hc C X (0 : SupportedAERVVolumeFunction hc C X k) = 0 := rfl

instance supportedVolumeFunctionAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    AddCommMonoid (SupportedAERVVolumeFunction hc C X k) where
  add_assoc f g h := supported_volume_function_forget_injective hc C X (by
    simp only [supported_volume_function_forget_add,add_assoc])
  add_comm f g := supported_volume_function_forget_injective hc C X (by
    simp only [supported_volume_function_forget_add,add_comm])
  zero_add f := supported_volume_function_forget_injective hc C X (by
    simp only [supported_volume_function_forget_add,supported_volume_function_forget_zero,zero_add])
  add_zero f := supported_volume_function_forget_injective hc C X (by
    simp only [supported_volume_function_forget_add,supported_volume_function_forget_zero,add_zero])
  nsmul := nsmulRec

def supportedVolumeFunctionForgetAddHom
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedAERVVolumeFunction hc C X k →+ AERVVolumeFunction hc C n k where
  toFun := supportedVolumeFunctionForget hc C X
  map_zero' := supported_volume_function_forget_zero hc C X
  map_add' := supported_volume_function_forget_add hc C X
end IntegrationInACVF.Section7
