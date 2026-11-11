import IntegrationSection5.UnaryConjugationGeometry
import Section5.RootConstruction

/-! Function and inverse identities for the matched unary-chain induction.
The predecessor supplies chain append and alternation lemmas directly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r s t : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {A' : DefSet (M := M) S 1 r} {B' : DefSet (M := M) S 1 s}
variable {F : DefSet (M := M) S 1 t}

theorem unaryConjugate_inverse (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (f : Map A B) (hf : Function.Bijective f) (z : B') :
    Map.inverse (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf) z =
      TA.toMap (Map.inverse f hf (TB.inverseMap z)) := by
  apply (unaryConjugate_bijective TA TB f hf).1
  rw [Map.apply_inverse]
  change z = TB.toMap (f (TA.inverseMap (TA.toMap (Map.inverse f hf (TB.inverseMap z)))))
  rw [TA.inverse_apply, Map.apply_inverse, TB.apply_inverse]

theorem special_split_inverse (TB : SpecialBijection B B') (R : SpecialBijection B F)
    (U : SpecialBijection B' F)
    (hR : ∀ b : B, R.toMap b = U.toMap (TB.toMap b)) (z : F) :
    TB.toMap (R.inverseMap z) = U.inverseMap z := by
  apply U.bijective.1
  rw [← hR, R.apply_inverse, U.apply_inverse]

theorem conjugate_tail_inverse (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (R : SpecialBijection B F) (U : SpecialBijection B' F)
    (hR : ∀ b : B, R.toMap b = U.toMap (TB.toMap b))
    (f : Map A B) (hf : Function.Bijective f) (z : F) :
    (Map.comp (Map.inverse (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf))
      U.inverseMap) z =
      (Map.comp TA.toMap (Map.comp (Map.inverse f hf) R.inverseMap)) z := by
  change Map.inverse (unaryConjugate TA TB f) _ (U.inverseMap z) = _
  rw [unaryConjugate_inverse]
  have hsplit := special_split_inverse TB R U hR z
  rw [← hsplit, TB.inverse_apply]
  rfl

theorem conjugate_tail_contractible (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (R : SpecialBijection B F) (U : SpecialBijection B' F)
    (hR : ∀ b : B, R.toMap b = U.toMap (TB.toMap b))
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible (Map.comp TA.toMap (Map.comp (Map.inverse f hf) R.inverseMap))) :
    Contractible (Map.comp (Map.inverse (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf))
      U.inverseMap) := by
  intro a b hab
  rw [conjugate_tail_inverse TA TB R U hR f hf a,
    conjugate_tail_inverse TA TB R U hR f hf b]
  exact hc a b hab

theorem special_comp_apply (T : SpecialBijection A B) (U : SpecialBijection B A')
    (h : (T.chain.append U.chain).Alternating none) (a : A) :
    (T.comp U h).toMap a = U.toMap (T.toMap a) := by
  have he := T.chain.append_toMap U.chain
  exact congrArg (fun g : Map A A' => g a) he

theorem special_comp_inverse (T : SpecialBijection A B) (U : SpecialBijection B A')
    (h : (T.chain.append U.chain).Alternating none) (z : A') :
    (T.comp U h).inverseMap z = T.inverseMap (U.inverseMap z) := by
  apply (T.comp U h).bijective.1
  rw [SpecialBijection.apply_inverse, special_comp_apply, T.apply_inverse, U.apply_inverse]

theorem special_refl_inverse (A : DefSet (M := M) S 1 m) (a : A) :
    (SpecialBijection.refl A).inverseMap a = a := by
  have h := (SpecialBijection.refl A).apply_inverse a
  exact h

end IntegrationInACVF.Section5
