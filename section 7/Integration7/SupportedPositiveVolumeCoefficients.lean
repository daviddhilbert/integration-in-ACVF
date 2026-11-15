import Integration7.SupportedVolumeFunctionAddition
import Integration7.AERVVolumePositiveCoefficientBilinearity

/-! Actual positive coefficient multiplication retains support and
descends to the supported AE quotient, with the original fibre product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k p : ℕ}

theorem selected_volume_family_left_product_supported
    {C : BaseContext M} {X : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) :
    ∀ q : (selectedVolumeFamilyLeftProduct U F).domain, q.val.1 ∈ X.carrier := by
  rintro ⟨q,z,hz⟩
  have he := congrArg Prod.fst hz
  change z.val.1=q.1 at he
  have hmem := (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain z.val.1 z.val.2).mp z.property
  exact he ▸ hF ⟨(z.val.1,z.val.2 ∘ Fin.castAdd U.underlying.obj.arity),hmem.1⟩

def supportedPositiveVolumeCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    PositiveVolumeBlowupClasses hc C p → SupportedAERVVolumeFunction hc C X k →
      SupportedAERVVolumeFunction hc C X ((p+1)+k) :=
  Quotient.map₂ (fun U F => ⟨_,⟨selectedVolumeFamilyLeftProduct U F.2.val,
      selected_volume_family_left_product_supported U F.2.val F.2.property⟩⟩)
    (fun U V hUV F G hFG => ae_volume_positive_coefficient_product_congr hc C U V
      F.2.val G.2.val hUV hFG)

theorem supported_volume_forget_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (u : PositiveVolumeBlowupClasses hc C p) (f : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionForget hc C X (supportedPositiveVolumeCoefficientProduct hc C X u f) =
      aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u
        (supportedVolumeFunctionForget hc C X f) :=
  Quotient.inductionOn₂ u f (fun _ _ => rfl)

def supportedPositiveVolumeCoefficientBiadditive
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    PositiveVolumeBlowupClasses hc C p →+
      (SupportedAERVVolumeFunction hc C X k →+ SupportedAERVVolumeFunction hc C X ((p+1)+k)) where
  toFun u := {
    toFun := supportedPositiveVolumeCoefficientProduct hc C X u
    map_zero' := supported_volume_function_forget_injective hc C X (by
      rw [supported_volume_forget_positive_coefficient,supported_volume_function_forget_zero,
        supported_volume_function_forget_zero,ae_rv_volume_positive_coefficient_zero_function])
    map_add' f g := supported_volume_function_forget_injective hc C X (by
      rw [supported_volume_forget_positive_coefficient,supported_volume_function_forget_add,
        ae_rv_volume_positive_coefficient_add_function,supported_volume_function_forget_add,
        supported_volume_forget_positive_coefficient,supported_volume_forget_positive_coefficient]) }
  map_zero' := AddMonoidHom.ext (fun f => supported_volume_function_forget_injective hc C X (by
    change supportedVolumeFunctionForget hc C X (supportedPositiveVolumeCoefficientProduct hc C X 0 f) =
      supportedVolumeFunctionForget hc C X 0
    rw [supported_volume_forget_positive_coefficient,ae_rv_volume_positive_zero_coefficient,
      supported_volume_function_forget_zero]))
  map_add' u v := AddMonoidHom.ext (fun f => supported_volume_function_forget_injective hc C X (by
    change supportedVolumeFunctionForget hc C X (supportedPositiveVolumeCoefficientProduct hc C X (u+v) f) =
      supportedVolumeFunctionForget hc C X
        (supportedPositiveVolumeCoefficientProduct hc C X u f + supportedPositiveVolumeCoefficientProduct hc C X v f)
    rw [supported_volume_forget_positive_coefficient,ae_rv_volume_positive_coefficient_add,
      supported_volume_function_forget_add,supported_volume_forget_positive_coefficient,
      supported_volume_forget_positive_coefficient]))
end IntegrationInACVF.Section7
