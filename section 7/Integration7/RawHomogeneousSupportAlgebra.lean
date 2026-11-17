module

public import Integration7.RawSupportedNonemptyFubini
public import Integration7.SupportedPositiveGradedActions
public import Integration7.NormalizedOrdinaryVolumeSupports

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The literal supported homogeneous families are closed under zero,
addition and every actual coefficient action. Thus their coefficient
span does not introduce functions with larger support. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))

theorem raw_volume_component_support_degree_heq {i j : ℕ} (h : i=j)
    {f : AEVolumeFunctionComponent hc C n i} {g : AEVolumeFunctionComponent hc C n j}
    (he : HEq f g) (hf : HasRawVolumeComponentSupport hc C X i f) :
    HasRawVolumeComponentSupport hc C X j g := by
  cases h
  cases he
  exact hf

theorem raw_volume_component_zero_has_support (j : ℕ) :
    HasRawVolumeComponentSupport hc C X j 0 := by
  cases j with
  | zero => exact ⟨0,ordinaryZeroVolumeFamily C (n+1),fun q => False.elim q.property,rfl⟩
  | succ k => exact ⟨0,supported_volume_function_forget_zero hc C X⟩

theorem raw_volume_component_add_preserves_support (j : ℕ) (f g : AEVolumeFunctionComponent hc C n j)
    (hf : HasRawVolumeComponentSupport hc C X j f) (hg : HasRawVolumeComponentSupport hc C X j g) :
    HasRawVolumeComponentSupport hc C X j (f+g) := by
  cases j with
  | succ k =>
    obtain ⟨F,rfl⟩ := hf
    obtain ⟨G,rfl⟩ := hg
    exact ⟨F+G,supported_volume_function_forget_add hc C X F G⟩
  | zero =>
    obtain ⟨a,F,hF,rfl⟩ := hf
    obtain ⟨b,G,hG,rfl⟩ := hg
    refine ⟨1+(a+b),F.coprod G,?_,rfl⟩
    rintro ⟨q,hq⟩
    rcases hq with ⟨p,hp⟩ | ⟨p,hp⟩
    · have he := congrArg Prod.fst hp
      change p.val.1=q.1 at he
      exact he ▸ hF p
    · have he := congrArg Prod.fst hp
      change p.val.1=q.1 at he
      exact he ▸ hG p

theorem raw_volume_component_coefficient_preserves_support (i j : ℕ)
    (u : RVVolumeBlowupClasses hc C i) (f : AEVolumeFunctionComponent hc C n j)
    (hf : HasRawVolumeComponentSupport hc C X j f) :
    HasRawVolumeComponentSupport hc C X (i+j)
      (aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u f) := by
  cases j with
  | succ k =>
    obtain ⟨g,rfl⟩ := hf
    let v := supportedPositiveComponentAction hc C X i k u g
    have hv := supported_positive_component_action_forget hc C X i k u g
    have hs := graded_shift_component_action_heq (aeVolumeFunctionGradedAction hc C n) 1 i k u
      (supportedVolumeFunctionForget hc C X g)
    exact raw_volume_component_support_degree_heq hc C X (i := (i+k)+1) (j := i+(k+1)) (by omega)
      ((heq_of_eq hv).trans hs) (show HasRawPositiveVolumeSupport hc C X
        (supportedVolumeFunctionForget hc C X v) from ⟨v,rfl⟩)
  | zero =>
    cases i with
    | zero =>
      obtain ⟨a,F,hF,rfl⟩ := hf
      induction u using Quotient.inductionOn with
      | h Z =>
        refine ⟨a+Z.obj.arity,F.prodZero Z,?_,rfl⟩
        intro q
        have hm := (mem_mixed_rv_factor_domain F.domain Z.obj.domain q.val.1 q.val.2).mp q.property
        exact hF ⟨(q.val.1,q.val.2 ∘ Fin.castAdd Z.obj.arity),hm.1⟩
    | succ p =>
      obtain ⟨a,F,hF,rfl⟩ := hf
      induction u using Quotient.inductionOn with
      | h U =>
        exact ⟨Quotient.mk _ ⟨_,⟨selectedOrdinaryFamilyPositiveProduct U F,
          selected_ordinary_positive_product_supported U F hF⟩⟩,rfl⟩
end IntegrationInACVF.Section7
