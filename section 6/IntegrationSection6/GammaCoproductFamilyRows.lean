import IntegrationSection6.GammaCoproductFamilies
import IntegrationSection6.GammaFamilyRows

/-! Literal rows of the uniform tagged coproduct family. Its tags preserve
the actual VF parameter tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b c k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem point_family_image_row_iff
    (f : Point (M := M) p a → Point (M := M) p c)
    (T : (Fin a → RV (M := M)) → (Fin c → RV (M := M)))
    (hf : ∀ q, f q = (q.1,T q.2)) (D : Set (Point (M := M) p a))
    (z : Fin p → VF (M := M)) (w : Fin c → RV (M := M)) :
    (∃ q, q ∈ D ∧ f q = (z,w)) ↔ ∃ x : Fin a → RV (M := M), (z,x) ∈ D ∧ T x = w := by
  constructor
  · rintro ⟨q,hq,he⟩
    have hz : q.1 = z := (congrArg Prod.fst (hf q)).symm.trans (congrArg Prod.fst he)
    have hqz : q = (z,q.2) := Prod.ext hz rfl
    exact ⟨q.2,(Iff.of_eq (congrArg (fun q => q ∈ D) hqz)).mp hq,
      (congrArg Prod.snd (hf q)).symm.trans (congrArg Prod.snd he)⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨(z,x),hx,(hf (z,x)).trans (Prod.ext rfl he)⟩

theorem point_family_relation_row_iff
    (f : Point (M := M) p a → Point (M := M) p c)
    (T : (Fin a → RV (M := M)) → (Fin c → RV (M := M)))
    (hf : ∀ q, f q = (q.1,T q.2)) (D : Set (Point (M := M) p a))
    (R : Point (M := M) p a → Point (M := M) 0 k → Prop)
    (z : Fin p → VF (M := M)) (w : Fin c → RV (M := M)) (y : Fin k → RV (M := M)) :
    (∃ q, (q ∈ D ∧ f q = (z,w)) ∧ R q (Fin.elim0,y)) ↔
      ∃ x : Fin a → RV (M := M), (z,x) ∈ D ∧ T x = w ∧ R (z,x) (Fin.elim0,y) := by
  constructor
  · rintro ⟨q,⟨hq,he⟩,hr⟩
    have hz : q.1 = z := (congrArg Prod.fst (hf q)).symm.trans (congrArg Prod.fst he)
    have hqz : q = (z,q.2) := Prod.ext hz rfl
    exact ⟨q.2,(Iff.of_eq (congrArg (fun q => q ∈ D) hqz)).mp hq,
      (congrArg Prod.snd (hf q)).symm.trans (congrArg Prod.snd he),
      (Iff.of_eq (congrArg (fun q => R q (Fin.elim0,y)) hqz)).mp hr⟩
  · rintro ⟨x,hx,he,hr⟩
    exact ⟨(z,x),⟨hx,(hf (z,x)).trans (Prod.ext rfl he)⟩,hr⟩

theorem GammaRVFamilyFormula.coprod_row_domain (F : GammaRVFamilyFormula B p a k)
    (G : GammaRVFamilyFormula B p b k) (z : Fin p → VF (M := M))
    (w : Fin (1+(a+b)) → RV (M := M)) :
    w ∈ (F.coprod G).rowDomain z ↔
      (∃ x : Fin a → RV (M := M), x ∈ F.rowDomain z ∧ @rvLeftTag M N hN a b x = w) ∨
      ∃ y : Fin b → RV (M := M), y ∈ G.rowDomain z ∧ @rvRightTag M N hN b a y = w := by
  exact or_congr
    (point_family_image_row_iff _ _
      (fun q => @familyLeftTagMap_value M sM hM B.real p a b ⟨q,Set.mem_univ _⟩) F.domain z w)
    (point_family_image_row_iff _ _
      (fun q => @familyRightTagMap_value M sM hM B.real p a b ⟨q,Set.mem_univ _⟩) G.domain z w)

theorem GammaRVFamilyFormula.coprod_row_volume (F : GammaRVFamilyFormula B p a k)
    (G : GammaRVFamilyFormula B p b k) (z : Fin p → VF (M := M))
    (w : Fin (1+(a+b)) → RV (M := M)) (v : Fin k → RV (M := M)) :
    (F.coprod G).rowVolume z w v ↔
      (∃ x : Fin a → RV (M := M), x ∈ F.rowDomain z ∧ @rvLeftTag M N hN a b x = w ∧ F.rowVolume z x v) ∨
      ∃ y : Fin b → RV (M := M), y ∈ G.rowDomain z ∧ @rvRightTag M N hN b a y = w ∧ G.rowVolume z y v := by
  exact or_congr
    (point_family_relation_row_iff _ _
      (fun q => @familyLeftTagMap_value M sM hM B.real p a b ⟨q,Set.mem_univ _⟩) F.domain F.volume z w v)
    (point_family_relation_row_iff _ _
      (fun q => @familyRightTagMap_value M sM hM B.real p a b ⟨q,Set.mem_univ _⟩) G.domain G.volume z w v)

theorem GammaRVFamilyFormula.coprod_row_support (F : GammaRVFamilyFormula B p a k)
    (G : GammaRVFamilyFormula B p b k) (z : Fin p → VF (M := M))
    (w : Fin (1+(a+b)) → RV (M := M)) (v : Fin k → RV (M := M))
    (h : (F.coprod G).rowVolume z w v) : w ∈ (F.coprod G).rowDomain z := by
  rcases h with ⟨x,hx,_⟩ | ⟨y,hy,_⟩
  · exact Or.inl ⟨x,hx⟩
  · exact Or.inr ⟨y,hy⟩

end IntegrationInACVF.Section6
