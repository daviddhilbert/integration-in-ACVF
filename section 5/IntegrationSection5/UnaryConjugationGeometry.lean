import IntegrationSection5.UnaryCellEquivalence

/-! Two fixed RV cells retain the open-to-open geometry after actual
special bijections on the two sides. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r s : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {A' : DefSet (M := M) S 1 r} {B' : DefSet (M := M) S 1 s}

def unaryConjugate (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (f : Map A B) : Map A' B' := Map.comp TB.toMap (Map.comp f TA.inverseMap)

theorem unaryConjugate_bijective (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (f : Map A B) (hf : Function.Bijective f) : Function.Bijective (unaryConjugate TA TB f) :=
  TB.bijective.comp (hf.comp TA.equiv.symm.bijective)

theorem unaryConjugate_image (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (f : Map A B) (E : Set (Point (M := M) 1 r)) :
    unaryImage f (unaryImage TA.inverseMap E) =
      unaryImage TB.inverseMap (unaryImage (unaryConjugate TA TB f) E) := by
  symm
  change unaryImage TB.inverseMap (unaryImage (TB.toMap ∘ (f ∘ TA.inverseMap)) E) = _
  rw [unaryImage_comp, unaryImage_comp]
  exact unaryImage_inverse_apply TB.toMap TB.bijective _ (unaryImage_subset f _)

theorem cellwiseOpenEquivalence_conjugate
    (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (f : Map A B) (hg : CellwiseOpenEquivalence f) :
    CellwiseOpenEquivalence (unaryConjugate TA TB f) := by
  intro E hEA hsrc htar
  obtain ⟨a, ha⟩ := hsrc
  obtain ⟨b, hb⟩ := htar
  let D := unaryImage TA.inverseMap E
  let F := unaryImage (unaryConjugate TA TB f) E
  have hDcell : ∃ a : A, ∀ p ∈ D, SameRV p a.val := by
    refine ⟨TA.inverseMap a, ?_⟩
    rintro p ⟨q, hq, rfl⟩
    exact TA.inverse_contractible q a (ha q.val hq)
  have hFcell : ∃ b : B, ∀ q ∈ unaryImage f D, SameRV q b.val := by
    refine ⟨TB.inverseMap b, ?_⟩
    rw [unaryConjugate_image TA TB f E]
    rintro p ⟨q, hq, rfl⟩
    exact TB.inverse_contractible q b (hb q.val hq)
  have hOld := hg D (unaryImage_subset TA.inverseMap E) hDcell hFcell
  have hSrc := inverse_special_open_iff TA a E hEA
    (fun p hp => ((sameRV_iff _ _).mp (ha p hp)).2)
  have hTar := inverse_special_open_iff TB b F (unaryImage_subset (unaryConjugate TA TB f) E)
    (fun p hp => ((sameRV_iff _ _).mp (hb p hp)).2)
  rw [unaryConjugate_image TA TB f E] at hOld
  exact (hSrc.trans hOld).trans hTar.symm

end IntegrationInACVF.Section5
