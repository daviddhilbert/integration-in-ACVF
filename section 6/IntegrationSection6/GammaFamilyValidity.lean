import IntegrationSection6.GammaTuplePromotion
import Section3.GammaProjection

/-! Validity loci for finite formula families are genuine original-Gamma
sets. Universal row inclusion is the complement of a projected
counterexample, with all sorted guards retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ}

theorem gamma_family_row_subset_definable (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    {A C : Set (Fin (n+m) → M)} (hA : DefinableOverBase B (Fin.append sa sb) A)
    (hC : DefinableOverBase B (Fin.append sa sb) C) :
    DefinableOverBase B sa {a | (∀ i, sortEval (sa i) (a i)) ∧
      ∀ b : Fin m → M, Fin.append a b ∈ A → Fin.append a b ∈ C} := by
  let D := A ∩ (sortedUniverse (Fin.append sa sb) \ C)
  have hD : DefinableOverBase B (Fin.append sa sb) D := hA.inter hC.compl
  have hp := hD.image_real (Fin.castAdd m)
  have he : (Fin.append sa sb) ∘ Fin.castAdd m = sa := by
    funext i
    exact Fin.append_left sa sb i
  rw [he] at hp
  have hg := hp.compl
  convert hg using 1
  ext a
  constructor
  · rintro ⟨ha,hall⟩
    refine ⟨ha,?_⟩
    rintro ⟨x,⟨hxA,hxsort,hxC⟩,hx⟩
    have hx' : Fin.append a (fun j => x (Fin.natAdd n j)) = x := by
      rw [← hx]
      exact Fin.append_castAdd_natAdd
    have hC' := hall (fun j => x (Fin.natAdd n j)) (hx'.symm ▸ hxA)
    exact hxC (hx' ▸ hC')
  · rintro ⟨ha,hbad⟩
    refine ⟨ha,?_⟩
    intro b hab
    by_contra hc
    apply hbad
    refine ⟨Fin.append a b,⟨hab,hA.proper _ hab,hc⟩,?_⟩
    funext i
    exact Fin.append_left a b i

theorem gamma_family_row_eq_definable (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    {A C : Set (Fin (n+m) → M)} (hA : DefinableOverBase B (Fin.append sa sb) A)
    (hC : DefinableOverBase B (Fin.append sa sb) C) :
    DefinableOverBase B sa {a | (∀ i, sortEval (sa i) (a i)) ∧
      ∀ b : Fin m → M, Fin.append a b ∈ A ↔ Fin.append a b ∈ C} := by
  have h := (gamma_family_row_subset_definable sa sb hA hC).inter
    (gamma_family_row_subset_definable sa sb hC hA)
  convert h using 1
  ext a
  constructor
  · rintro ⟨ha,h⟩
    exact ⟨⟨ha,fun b hb => (h b).mp hb⟩,⟨ha,fun b hb => (h b).mpr hb⟩⟩
  · rintro ⟨⟨ha,hac⟩,⟨_,hca⟩⟩
    exact ⟨ha,fun b => ⟨hac b,hca b⟩⟩

end IntegrationInACVF.Section6
