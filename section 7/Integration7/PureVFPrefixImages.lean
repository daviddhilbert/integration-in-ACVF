module

public import Integration7.PureVFCoordinateImageComposition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The support of an iterated head contraction is the literal image
under deletion of its initial VF coordinates. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] {S : Set M}

def vfPrefixRetainedIndex : (r n : ℕ) → Fin (n+1) → Fin ((n+r)+1)
  | 0,_ => id
  | r+1,n => Fin.succ ∘ vfPrefixRetainedIndex r n

theorem vf_prefix_retained_index_value (r n : ℕ) (i : Fin (n+1)) :
    (vfPrefixRetainedIndex r n i).val = r+i.val := by
  induction r with
  | zero => exact (Nat.zero_add i.val).symm
  | succ r ih =>
    change (vfPrefixRetainedIndex r n i).val+1 = _
    omega

def pureVFPrefixImage : (r n : ℕ) →
    DefSet (rawVFSpace (M := M) ((n+r)+1)) S → DefSet (rawVFSpace (M := M) (n+1)) S
  | 0,_,X => X
  | r+1,n,X => pureVFPrefixImage r n (pureVFCoordinateImage X Fin.succ)

theorem pure_vf_prefix_image_eq : ∀ (r n : ℕ)
    (X : DefSet (rawVFSpace (M := M) ((n+r)+1)) S),
    pureVFPrefixImage r n X = pureVFCoordinateImage X (vfPrefixRetainedIndex r n) := by
  intro r
  induction r with
  | zero => intro n X; exact (pure_vf_coordinate_image_id X).symm
  | succ r ih =>
    intro n X
    change pureVFPrefixImage r n (pureVFCoordinateImage X Fin.succ) = _
    rw [ih,pure_vf_coordinate_image_comp]
    rfl
end IntegrationInACVF.Section7
