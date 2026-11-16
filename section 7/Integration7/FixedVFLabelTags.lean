module

public import Integration7.VFVolumeObjects
public import Section4.RVTagging
public import Section4.RVCoproduct

@[expose] public section

/-! Disjoint RV labels tag mixed domains without adding VF coordinates.
The actual maps fix VF tuples and preserve finiteness of RV fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}

def fixedVFLeftTagMap (A : DefSet (rawMixedSpace (M := M) n a) S) (b : ℕ) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n (1+(a+b))) S) :=
  ((Map.fst (rawVFSpace n) (rawRVSpace a) S A).pair
    ((rvLeftTagMap (DefSet.univ (rawRVSpace a) S) b).comp
      (Map.snd (rawVFSpace n) (rawRVSpace a) S A))).toUniv

def fixedVFRightTagMap (B : DefSet (rawMixedSpace (M := M) n b) S) (a : ℕ) :
    Map B (DefSet.univ (rawMixedSpace (M := M) n (1+(a+b))) S) :=
  ((Map.fst (rawVFSpace n) (rawRVSpace b) S B).pair
    ((rvRightTagMap (DefSet.univ (rawRVSpace b) S) a).comp
      (Map.snd (rawVFSpace n) (rawRVSpace b) S B))).toUniv

theorem fixed_vf_left_tag_value (A : DefSet (rawMixedSpace (M := M) n a) S) (b : ℕ) (p : A) :
    (fixedVFLeftTagMap A b p).val = (p.val.1,rvLeftTag b p.val.2) := rfl

theorem fixed_vf_right_tag_value (B : DefSet (rawMixedSpace (M := M) n b) S) (a : ℕ) (p : B) :
    (fixedVFRightTagMap B a p).val = (p.val.1,rvRightTag a p.val.2) := rfl

theorem fixed_vf_left_tag_injective (A : DefSet (rawMixedSpace (M := M) n a) S) (b : ℕ) :
    Function.Injective (fixedVFLeftTagMap A b) := by
  intro p q h
  have hv := congrArg (fun r : DefSet.univ (rawMixedSpace (M := M) n (1+(a+b))) S => r.val) h
  have hx := congrArg Prod.fst hv
  have hr := congrArg Prod.snd hv
  exact Subtype.ext (Prod.ext hx (rvLeftTag_injective b hr))

theorem fixed_vf_right_tag_injective (B : DefSet (rawMixedSpace (M := M) n b) S) (a : ℕ) :
    Function.Injective (fixedVFRightTagMap B a) := by
  intro p q h
  have hv := congrArg (fun r : DefSet.univ (rawMixedSpace (M := M) n (1+(a+b))) S => r.val) h
  have hx := congrArg Prod.fst hv
  have hr := congrArg Prod.snd hv
  exact Subtype.ext (Prod.ext hx (rvRightTag_injective a hr))

theorem fixed_vf_left_tag_to_image_bijective (A : DefSet (rawMixedSpace (M := M) n a) S) (b : ℕ) :
    Function.Bijective (fixedVFLeftTagMap A b).toImage := by
  constructor
  · intro p q h
    apply fixed_vf_left_tag_injective A b
    exact Subtype.ext (congrArg (fun r : (fixedVFLeftTagMap A b).image => r.val) h)
  · rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩

theorem fixed_vf_right_tag_to_image_bijective (B : DefSet (rawMixedSpace (M := M) n b) S) (a : ℕ) :
    Function.Bijective (fixedVFRightTagMap B a).toImage := by
  constructor
  · intro p q h
    apply fixed_vf_right_tag_injective B a
    exact Subtype.ext (congrArg (fun r : (fixedVFRightTagMap B a).image => r.val) h)
  · rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩

def fixedVFUntagLeft (A : DefSet (rawMixedSpace (M := M) n a) S) (b : ℕ) :
    Map (fixedVFLeftTagMap A b).image A :=
  (fixedVFLeftTagMap A b).toImage.inverse (fixed_vf_left_tag_to_image_bijective A b)

def fixedVFUntagRight (B : DefSet (rawMixedSpace (M := M) n b) S) (a : ℕ) :
    Map (fixedVFRightTagMap B a).image B :=
  (fixedVFRightTagMap B a).toImage.inverse (fixed_vf_right_tag_to_image_bijective B a)

theorem fixed_vf_tagged_images_disjoint (A : DefSet (rawMixedSpace (M := M) n a) S)
    (B : DefSet (rawMixedSpace (M := M) n b) S) :
    Disjoint (fixedVFLeftTagMap A b).image.carrier (fixedVFRightTagMap B a).image.carrier := by
  apply Set.disjoint_left.mpr
  rintro p ⟨u,hu⟩ ⟨v,hv⟩
  exact rvTag_disjoint u.val.2 v.val.2 (congrArg Prod.snd (hu.trans hv.symm))

theorem fixed_vf_left_tag_finite_labels (A : DefSet (rawMixedSpace (M := M) n a) S) (b : ℕ)
    (hfin : ∀ x : Fin n → SpecialTransformations.Milestone0.Transfer.VFType (M := M),
      {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ A.carrier}.Finite) :
    ∀ x : Fin n → SpecialTransformations.Milestone0.Transfer.VFType (M := M),
      {r | (x,r) ∈ (fixedVFLeftTagMap A b).image.carrier}.Finite := by
  intro x
  apply ((hfin x).image (rvLeftTag b)).subset
  rintro r ⟨u,hu⟩
  change (u.val.1,rvLeftTag b u.val.2) = (x,r) at hu
  have hx := congrArg Prod.fst hu
  exact ⟨u.val.2,Eq.mp (congrArg (fun y => (y,u.val.2) ∈ A.carrier) hx) u.property,congrArg Prod.snd hu⟩

theorem fixed_vf_right_tag_finite_labels (B : DefSet (rawMixedSpace (M := M) n b) S) (a : ℕ)
    (hfin : ∀ x : Fin n → SpecialTransformations.Milestone0.Transfer.VFType (M := M),
      {r : Fin b → CanonicalRV.RVSort M | (x,r) ∈ B.carrier}.Finite) :
    ∀ x : Fin n → SpecialTransformations.Milestone0.Transfer.VFType (M := M),
      {r | (x,r) ∈ (fixedVFRightTagMap B a).image.carrier}.Finite := by
  intro x
  apply ((hfin x).image (rvRightTag a)).subset
  rintro r ⟨u,hu⟩
  change (u.val.1,rvRightTag a u.val.2) = (x,r) at hu
  have hx := congrArg Prod.fst hu
  exact ⟨u.val.2,Eq.mp (congrArg (fun y => (y,u.val.2) ∈ B.carrier) hx) u.property,congrArg Prod.snd hu⟩

end IntegrationInACVF.Section7
