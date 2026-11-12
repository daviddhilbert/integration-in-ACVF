import IntegrationSection6.GammaFamilyCardinality

/-! Existential and unique-output validity for full Gamma tuple families.
These quantify actual tuples and retain the sorted guards. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ}

theorem gamma_family_row_exists_definable (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    {P : Set (Fin (n+m) → M)} (hP : DefinableOverBase B (Fin.append sa sb) P) :
    DefinableOverBase B sa {a | ∃ b : Fin m → M, Fin.append a b ∈ P} := by
  have h := hP.image_real (Fin.castAdd m)
  have hs : Fin.append sa sb ∘ Fin.castAdd m = sa := by
    funext i
    exact Fin.append_left sa sb i
  rw [hs] at h
  convert h using 1
  apply Set.ext
  intro a
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨Fin.append a b,hb,funext (Fin.append_left a b)⟩
  · rintro ⟨z,hz,ha⟩
    refine ⟨z ∘ Fin.natAdd n,?_⟩
    have he : Fin.append a (z ∘ Fin.natAdd n) = z := by
      rw [← ha]
      exact Fin.append_castAdd_natAdd
    exact he.symm ▸ hz

theorem gamma_family_row_unique_definable (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    {P : Set (Fin (n+m) → M)} (hP : DefinableOverBase B (Fin.append sa sb) P) :
    DefinableOverBase B sa {a | ∃! b : Fin m → M, Fin.append a b ∈ P} := by
  have h := (gamma_family_row_exists_definable sa sb hP).inter
    (gamma_family_finite_bound_definable sa sb 1 hP)
  convert h using 1
  apply Set.ext
  intro a
  constructor
  · rintro ⟨b,hb,hu⟩
    have he : {x : Fin m → M | Fin.append a x ∈ P} = {b} := by
      apply Set.ext
      intro x
      exact ⟨fun hx => hu x hx,fun hx => (Set.mem_singleton_iff.mp hx).symm ▸ hb⟩
    refine ⟨⟨b,hb⟩,?_,?_⟩
    · intro i
      simpa only [Fin.append_left] using hP.proper _ hb (Fin.castAdd m i)
    · rw [he]
      exact ⟨Set.finite_singleton _,by simp⟩
  · rintro ⟨⟨b,hb⟩,_,hf,hc⟩
    refine ⟨b,hb,fun x hx => ?_⟩
    have hle := Set.encard_le_coe_iff_finite_ncard_le.mpr (And.intro hf hc)
    exact Set.encard_le_one_iff.mp hle x b hx hb

theorem gamma_family_row_forall_definable (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    {P : Set (Fin (n+m) → M)} (hP : DefinableOverBase B (Fin.append sa sb) P) :
    DefinableOverBase B sa {a | (∀ i, sortEval (sa i) (a i)) ∧
      ∀ b : Fin m → M, (∀ j, sortEval (sb j) (b j)) → Fin.append a b ∈ P} := by
  have hU := real_definableOverBase B (Fin.append sa sb) _
    (sortedUniverse_definable B.real (Fin.append sa sb))
  have h := gamma_family_row_subset_definable sa sb hU hP
  convert h using 1
  apply Set.ext
  intro a
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨ha,fun b hs => hb b (fun j => ?_)⟩
    simpa only [Fin.append_right] using hs (Fin.natAdd n j)
  · rintro ⟨ha,hb⟩
    refine ⟨ha,fun b hs => hb b (fun j => ?_)⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left] using ha i
    · simpa only [Fin.append_right] using hs i

end IntegrationInACVF.Section6
