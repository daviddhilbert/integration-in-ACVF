import Integration7.UnaryRelativeSpecialRealization
import Integration7.MixedJacobianOneOperations
import Integration7.SpecialVolumeJacobians
import IntegrationSection5.StandardContraction

/-! The actual natural map of every unary standard contraction has
VF Jacobian one almost everywhere. Its head is an actual special
bijection, and output RV labels do not change the VF determinant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem unary_relative_vf_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (f : SpecialTransformations.Section5.Map A B) (hf : SpecialRelative f 0) :
    VFAlmostEverywhere (rawSpecialSet hc A) (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1) := by
  obtain ⟨T,hT⟩ := specialRelative_unary_special f hf
  have he : T.toMap = f := by
    exact @SpecialTransformations.DefinableGeometry.Map.ext LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) A B T.toMap f hT
  rw [← he]
  exact (special_vf_jacobian_one hc C Nat.one_pos T).1

theorem ordered_unary_natural_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}
    (T : OrderedContractionProgram (C.base : Set M) A B) :
    VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc T.naturalMap) p 1) := by
  cases T with
  | step H tail =>
    apply vfJacobianOne_of_same_vf hc C Nat.one_pos (rawSpecialMap hc H.map) _ _
      (unary_relative_vf_jacobian_one hc C H.map H.special)
    intro p
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

theorem standard_unary_natural_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {a : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) :
    VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc T.naturalMap) p 1) := by
  let f := rawSpecialMap hc (vfPermutationBijection A σ)
  let g := rawSpecialMap hc T.program.naturalMap
  have hf := vfJacobianOne_of_preservesVF hc C Nat.one_pos f (by
    intro p
    funext i
    exact congrArg (fun j => p.val.1 j) (Subsingleton.elim _ _))
  have hg := ordered_unary_natural_jacobian_one hc C T.program
  have hcomp := vfJacobianOne_comp hc C Nat.one_pos f g
    (vfPermutationBijection_bijective A σ).1 hf hg
  apply vfJacobianOne_of_same_vf hc C Nat.one_pos (g.comp f) _ _ hcomp
  intro p
  funext i
  change (T.program.naturalMap (vfPermutationBijection A σ p)).val.1 i =
    (T.program.naturalMap (vfPermutationBijection A σ p)).val.1 (σ.symm i)
  exact congrArg (fun j => (T.program.naturalMap (vfPermutationBijection A σ p)).val.1 j)
    (Subsingleton.elim _ _)

end IntegrationInACVF.Section7
