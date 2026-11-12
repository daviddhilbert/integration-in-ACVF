import IntegrationSection6.FocusRootDomains

/-! Extend a focus equation in selected coordinates to the full tuple.
Other coordinates, including absorbing zero classes, remain unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section7

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] {n r : ℕ}

/-- The equation only uses selected variables; uniqueness in the other
variables comes from the required unchanged-coordinate equations. -/
theorem rootDomain_extend (f : Fin r ↪ Fin n) (j : Fin r)
    (R : Set (Fin r → M)) {t : Fin n → M}
    (ht : t ∘ f ∈ rootDomain R j) :
    t ∈ rootDomain {b | b ∘ f ∈ R} (f j) := by
  intro a ha
  have ha' : a ∘ f ∈ rawTupleFibre (t ∘ f) := fun i => ha (f i)
  obtain ⟨b,hb,huniq⟩ := ht (a ∘ f) ha'
  let c := Function.extend f b a
  have hc (i : Fin r) : c (f i) = b i := f.injective.extend_apply b a i
  have hcf : c ∘ f = b := funext hc
  have hcRV : c ∈ rawTupleFibre t := by
    intro i
    by_cases hi : ∃ l, f l = i
    · obtain ⟨l,rfl⟩ := hi
      rw [hc]
      exact hb.1 l
    · rw [show c i = a i from Function.extend_apply' _ _ _ hi]
      exact ha i
  have hcother (i : Fin n) (hi : i ≠ f j) : c i = a i := by
    by_cases hif : ∃ l, f l = i
    · obtain ⟨l,rfl⟩ := hif
      rw [hc]
      exact hb.2.2 l (fun h => hi (congrArg f h))
    · exact Function.extend_apply' _ _ _ hif
  refine ⟨c,⟨hcRV,by change c ∘ f ∈ R; rw [hcf]; exact hb.2.1,hcother⟩,?_⟩
  intro d hd
  have hd' : d ∘ f ∈ rawTupleFibre (t ∘ f) ∧ d ∘ f ∈ R ∧
      ∀ i, i ≠ j → d (f i) = a (f i) := by
    refine ⟨fun i => hd.1 (f i),hd.2.1,?_⟩
    intro i hi
    exact hd.2.2 (f i) (fun h => hi (f.injective h))
  have hdb := huniq (d ∘ f) hd'
  funext i
  by_cases hi : ∃ l, f l = i
  · obtain ⟨l,rfl⟩ := hi
    exact (congrFun hdb l).trans (hc l).symm
  · have hij : i ≠ f j := fun h => hi ⟨j,h.symm⟩
    exact (hd.2.2 i hij).trans (Function.extend_apply' _ _ _ hi).symm

theorem rootEquation_extend_definable (S : Set M) (f : Fin r ↪ Fin n)
    (R : Set (Fin r → M)) (hR : S.Definable LRV R) :
    S.Definable LRV {b : Fin n → M | b ∘ f ∈ R} := hR.preimage_comp f

end IntegrationInACVF.Section6
