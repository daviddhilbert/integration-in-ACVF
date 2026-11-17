module

public import Integration7.MixedJacobianOneOperations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A definable mixed bijection has nonzero VF Jacobian almost
everywhere, by differentiating it and its actual definable inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem mixed_bijective_jacobian_nonzero_ae
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (f : Map A B) (hf : Function.Bijective f) :
    VFAlmostEverywhere A (fun p => ∃ J : VFType (M := M),
      HasMixedVFJacobianAt f p J ∧ J ≠ 0) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  let g := f.inverse hf
  obtain ⟨E,hEA,hd,hE⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small hn f g
    (Map.finiteFibres_of_injective hf.1)
  have hChain : VFAlmostEverywhere A (fun p => ∃ J K : VFType (M := M),
      HasMixedVFJacobianAt f p J ∧ HasMixedVFJacobianAt g (f p) K ∧
      HasMixedVFJacobianAt (g.comp f) p (K*J)) := ⟨E,hEA,hd,hE⟩
  have hId := vfJacobianOne_of_preservesVF hc C hn (g.comp f)
    (fun p => congrArg (fun q : A => q.val.1) (Map.inverse_apply f hf p))
  apply (vfAlmostEverywhere_and hc C hChain hId).mono
  rintro p ⟨⟨J,K,hJ,_,hComp⟩,hOne⟩
  have he : K*J = 1 := hComp.unique hOne
  refine ⟨J,hJ,?_⟩
  intro hzero
  rw [hzero,mul_zero] at he
  exact zero_ne_one he

end IntegrationInACVF.Section7
