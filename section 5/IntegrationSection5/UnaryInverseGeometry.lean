import IntegrationSection5.UnaryOpenImages

/-! On any fixed final RV label tuple, the inverse of an actual unary
special bijection is a translation with fixed original RV labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem inverse_special_labels (T : SpecialBijection A B) (a b : B)
    (he : a.val.2 = b.val.2) : (T.inverseMap a).val.2 = (T.inverseMap b).val.2 := by
  apply T.chain.labels_eq_of (T.inverseMap a) (T.inverseMap b)
  change (T.toMap (T.inverseMap a)).val.2 = (T.toMap (T.inverseMap b)).val.2
  simpa only [T.apply_inverse] using he

theorem inverse_special_difference (T : SpecialBijection A B) (a b : B)
    (he : a.val.2 = b.val.2) :
    vfAt (T.inverseMap a).val 0 - vfAt (T.inverseMap b).val 0 = vfAt a.val 0 - vfAt b.val 0 := by
  have hout : (T.toMap (T.inverseMap a)).val.2 = (T.toMap (T.inverseMap b)).val.2 := by
    simpa only [T.apply_inverse] using he
  have h := T.chain.unary_sub (T.inverseMap a) (T.inverseMap b) hout
  change vfAt (T.toMap (T.inverseMap a)).val 0 - vfAt (T.toMap (T.inverseMap b)).val 0 =
    vfAt (T.inverseMap a).val 0 - vfAt (T.inverseMap b).val 0 at h
  simpa only [T.apply_inverse] using h.symm

theorem inverse_special_affine (T : SpecialBijection A B) (a b : B)
    (he : a.val.2 = b.val.2) :
    (T.inverseMap a).val =
      unaryReframe (vfAt b.val 0 - vfAt (T.inverseMap b).val 0) (T.inverseMap b).val.2 a.val := by
  refine Prod.ext ?_ (inverse_special_labels T a b he)
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change vfAt (T.inverseMap a).val 0 =
    vfAt a.val 0 - (vfAt b.val 0 - vfAt (T.inverseMap b).val 0)
  calc
    _ = (vfAt (T.inverseMap a).val 0 - vfAt (T.inverseMap b).val 0) +
        vfAt (T.inverseMap b).val 0 := (sub_add_cancel _ _).symm
    _ = (vfAt a.val 0 - vfAt b.val 0) + vfAt (T.inverseMap b).val 0 := by
      rw [inverse_special_difference T a b he]
    _ = _ := by abel

theorem inverse_special_image_eq (T : SpecialBijection A B) (b : B)
    (E : Set (Point (M := M) 1 l)) (hEB : E ⊆ carrier B)
    (hlabel : ∀ p ∈ E, p.2 = b.val.2) :
    unaryImage T.inverseMap E =
      unaryReframe (vfAt b.val 0 - vfAt (T.inverseMap b).val 0) (T.inverseMap b).val.2 '' E := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, ha, (inverse_special_affine T a b (hlabel a.val ha)).symm⟩
  · rintro ⟨p, hp, he⟩
    let a : B := ⟨p, hEB hp⟩
    exact ⟨a, hp, (inverse_special_affine T a b (hlabel p hp)).trans he⟩

theorem inverse_special_open_images (T : SpecialBijection A B) :
    CellwiseOpenMap T.inverseMap := by
  intro E hE hEB hcell
  obtain ⟨b, hb⟩ := hcell
  rw [inverse_special_image_eq T b E hEB (fun p hp => ((sameRV_iff _ _).mp (hb p hp)).2)]
  exact unaryReframe_open_polydisc _ _ hE

end IntegrationInACVF.Section5
