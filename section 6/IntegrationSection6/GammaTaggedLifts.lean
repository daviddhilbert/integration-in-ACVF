import IntegrationSection6.RVLabelMap
import IntegrationSection6.GammaRealImages
import Section4.RVTagging

/-! Tagged mixed sets and their original-Gamma isomorphisms. The tags
are exactly those used in the inherited finite RV coproduct. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m r : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def taggedLeftSet (A : Set (Point (M := M) n m)) (r : ℕ) :
    Set (Point (M := M) n (1+(m+r))) :=
  {p | ∃ a : A, (a.val.1,@rvLeftTag M N hN m r a.val.2) = p}

def taggedRightSet (A : Set (Point (M := M) n r)) (m : ℕ) :
    Set (Point (M := M) n (1+(m+r))) :=
  {p | ∃ a : A, (a.val.1,@rvRightTag M N hN r m a.val.2) = p}

theorem tagged_sets_disjoint (A : Set (Point (M := M) n m)) (D : Set (Point (M := M) n r)) :
    Disjoint (taggedLeftSet A r) (taggedRightSet D m) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨a,ha⟩ ⟨d,hd⟩
  exact @rvTag_disjoint M N hN m r a.val.2 d.val.2 (congrArg Prod.snd (ha.trans hd.symm))

def gammaIso_leftTag (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A) (r : ℕ) :
    GammaIso B A (taggedLeftSet A r) := by
  let F := @rvLeftTagMap M N hN B.real m
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N m) B.real) r
  let G := mapRVLabels n B.real F
  apply gammaIso_realImage A hA G
  intro a b he
  have hv := congrArg (fun p => p.val.1) he
  have ht := congrArg (fun p => p.val.2) he
  apply Subtype.ext
  refine Prod.ext hv ?_
  exact @rvLeftTag_injective M N hN m r _ _ ht

def gammaIso_rightTag (A : Set (Point (M := M) n r)) (hA : GammaSetDefinable B A) (m : ℕ) :
    GammaIso B A (taggedRightSet A m) := by
  let F := @rvRightTagMap M N hN B.real r
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N r) B.real) m
  let G := mapRVLabels n B.real F
  apply gammaIso_realImage A hA G
  intro a b he
  have hv := congrArg (fun p => p.val.1) he
  have ht := congrArg (fun p => p.val.2) he
  apply Subtype.ext
  refine Prod.ext hv ?_
  exact @rvRightTag_injective M N hN r m _ _ ht

end IntegrationInACVF.Section6
