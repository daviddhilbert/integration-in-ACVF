module

public import Integration7.HeadTailPermutationFibreMaps
public import IntegrationSection5.RelativeFibreBijection
public import IntegrationSection6.SpecialEqualityTransport

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Reordering frozen VF coordinates preserves actual relative specialness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}

theorem head_tail_permutation_special_relative
    {A : DefSet (M := M) S (n+1) a} {B : DefSet (M := M) S (n+1) b}
    (f : Map A B) (hf : SpecialRelative f 0) (τ : Equiv.Perm (Fin n)) :
    SpecialRelative (vfPermutedMap f (headTailPerm τ)) 0 := by
  let hi := hf.choose
  let hI := vfPermutedMap_relative f (headTailPerm τ) hi
  refine ⟨hI,?_⟩
  intro u
  let v := u ∘ (headTailPerm τ).symm
  let hR := head_tail_permutation_fibre_base (S := S) τ u
  obtain ⟨T,hT⟩ := hf.choose_spec v
  let F := T.extendBase hR
  let U := coordinateFibre (vfPermutationImage A (headTailPerm τ)) 0 u
  let V := coordinateFibre (vfPermutationImage B (headTailPerm τ)) 0 u
  have hA : extendBase (coordinateFibre A 0 v) hR = U :=
    defSet_eq_of_carrier_eq (head_tail_permutation_fibre_carrier A τ u).symm
  have hB : extendBase (coordinateFibre B 0 v) hR = V :=
    defSet_eq_of_carrier_eq (head_tail_permutation_fibre_carrier B τ u).symm
  refine ⟨specialCastBoth F hA hB,?_⟩
  intro p
  let q : coordinateFibre A 0 v :=
    ⟨p.val,(Set.ext_iff.mp (head_tail_permutation_fibre_carrier A τ u) p.val).mp p.property⟩
  apply Subtype.ext
  calc
    ((specialCastBoth F hA hB).toMap p).val = (F.toMap ⟨q.val,q.property⟩).val :=
      specialCastBoth_value F hA hB p ⟨q.val,q.property⟩ rfl
    _ = (T.toMap q).val := T.chain.extendBase_apply hR q
    _ = (coordinateFibreMap f 0 hi v q).val := congrArg Subtype.val (hT q)
    _ = (coordinateFibreMap (vfPermutedMap f (headTailPerm τ)) 0 hI u p).val :=
      (head_tail_permutation_fibre_map f hi τ u p).symm

end IntegrationInACVF.Section7
