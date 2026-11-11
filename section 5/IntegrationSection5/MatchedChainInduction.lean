import IntegrationSection5.MatchedFocusStep

/-! Matching a complete prepared target chain in VF arity one.
The open-to-open geometric input remains separate from its 3.21 producer. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {l r : ℕ}
variable {B : DefSet (M := M) S 1 l} {F : DefSet (M := M) S 1 r}

theorem matched_chain_induction (R : Chain S 1 B F) :
    R.Alternating none →
    ∀ {m : ℕ} {A : DefSet (M := M) S 1 m}
      (f : Map A B) (hf : Function.Bijective f),
      Contractible f → CellwiseOpenEquivalence f →
      IsRVPullback (carrier A) → IsRVPullback (carrier B) → IsRVPullback (carrier F) →
      (∃ j : Fin m, Tagged (carrier A) 0 j) →
      Contractible (Map.comp (Map.inverse f hf) (Map.inverse R.toMap R.bijective)) →
      ∃ d : ℕ, ∃ A' : DefSet (M := M) S 1 d, ∃ TA : SpecialBijection A A',
        TA.chain.Alternating (some false) ∧ IsRVPullback (carrier A') ∧
        (∃ j : Fin d, Tagged (carrier A') 0 j) ∧
        Contractible (Map.comp R.toMap (Map.comp f TA.inverseMap)) ∧
        Contractible (Map.comp TA.toMap
          (Map.comp (Map.inverse f hf) (Map.inverse R.toMap R.bijective))) := by
  induction R with
  | nil B =>
    intro hR m A f hf hc hg hA hB hF hTag hFinal
    refine ⟨m, A, SpecialBijection.refl A, trivial, hA, hTag, ?_, hFinal⟩
    intro a b hab
    change SameRV (f ((SpecialBijection.refl A).inverseMap a)).val
      (f ((SpecialBijection.refl A).inverseMap b)).val
    rw [special_refl_inverse, special_refl_inverse]
    exact hc a b hab
  | @cons l0 l1 r0 B0 C0 F0 p tail ih =>
    intro hR m A f hf hc hg hA hB hF hTag hFinal
    cases p with
    | canonical _ =>
      let R0 : SpecialBijection B0 F0 := ⟨.cons (.canonical B0) tail, hR⟩
      let TB := SpecialBijection.canonical B0
      let U : SpecialBijection (canonicalImage B0) F0 :=
        ⟨tail, tail.alternating_none (some false) hR.2⟩
      let T0 := SpecialBijection.refl A
      let g := unaryConjugate T0 TB f
      have hgf : Function.Bijective g := unaryConjugate_bijective T0 TB f hf
      have hgc : Contractible g :=
        contractible_comp (Map.comp f T0.inverseMap) TB.toMap
          (contractible_comp T0.inverseMap f T0.inverse_contractible hc) (canonical_contractible B0)
      have hgg := cellwiseOpenEquivalence_conjugate T0 TB f hg
      have hsplit : ∀ b : B0, R0.toMap b = U.toMap (TB.toMap b) := fun _ => rfl
      have hGFinal : Contractible (Map.comp (Map.inverse g hgf) U.inverseMap) :=
        conjugate_tail_contractible T0 TB R0 U hsplit f hf hFinal
      obtain ⟨d, A', T, hAlt, hA', hTag', hForward, hReverse⟩ :=
        ih U.alternating g hgf hgc hgg hA (TB.preserves_pullback hB) hF hTag hGFinal
      refine ⟨d, A', T, hAlt, hA', hTag', ?_, ?_⟩
      · intro a b hab
        have h := hForward a b hab
        change SameRV
          (U.toMap (TB.toMap (f (T0.inverseMap (T.inverseMap a))))).val
          (U.toMap (TB.toMap (f (T0.inverseMap (T.inverseMap b))))).val at h
        rw [special_refl_inverse, special_refl_inverse] at h
        exact h
      · intro a b hab
        have h := hReverse a b hab
        change SameRV (T.toMap ((Map.comp (Map.inverse g hgf) U.inverseMap) a)).val
          (T.toMap ((Map.comp (Map.inverse g hgf) U.inverseMap) b)).val at h
        rw [conjugate_tail_inverse T0 TB R0 U hsplit f hf a,
          conjugate_tail_inverse T0 TB R0 U hsplit f hf b] at h
        exact h
    | @centripetal l i k D =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      obtain ⟨j, hTag⟩ := hTag
      let R0 : SpecialBijection B0 F0 := ⟨.cons (.centripetal D) tail, hR⟩
      let TB := SpecialBijection.centripetal D
      let U : SpecialBijection D.etaImage F0 :=
        ⟨tail, tail.alternating_none (some true) hR.2⟩
      let DA := pulledFocus f hf hc D hA hB hTag
      let T1 := focussedCanonical DA
      let g := unaryConjugate T1 TB f
      have hgf : Function.Bijective g := unaryConjugate_bijective T1 TB f hf
      have hsplit : ∀ b : B0, R0.toMap b = U.toMap (TB.toMap b) := fun _ => rfl
      obtain ⟨hgc, hgg, hGFinal⟩ := matched_focus_step f hf hc hg D hA hB hF hTag R0 U hsplit hFinal
      have hA1 : IsRVPullback (carrier (canonicalImage DA.etaImage)) := T1.preserves_pullback hA
      have hTag1 := focussedCanonical_tagged DA
      obtain ⟨d, A', T2, hAlt2, hA', hTag', hForward, hReverse⟩ :=
        ih U.alternating g hgf hgc hgg hA1 (TB.preserves_pullback hB) hF hTag1 hGFinal
      have hComp : (T1.chain.append T2.chain).Alternating none :=
        T1.chain.append_alternating T2.chain none T1.alternating hAlt2
      have hCompPrev : (T1.chain.append T2.chain).Alternating (some false) :=
        T1.chain.append_alternating T2.chain (some false) (focussedCanonical_alternating DA) hAlt2
      let T := T1.comp T2 hComp
      refine ⟨d, A', T, hCompPrev, hA', hTag', ?_, ?_⟩
      · intro a b hab
        change SameRV (R0.toMap (f ((T1.comp T2 hComp).inverseMap a))).val
          (R0.toMap (f ((T1.comp T2 hComp).inverseMap b))).val
        rw [special_comp_inverse T1 T2 hComp a, special_comp_inverse T1 T2 hComp b]
        exact hForward a b hab
      · intro a b hab
        change SameRV
          ((T1.comp T2 hComp).toMap ((Map.comp (Map.inverse f hf) R0.inverseMap) a)).val
          ((T1.comp T2 hComp).toMap ((Map.comp (Map.inverse f hf) R0.inverseMap) b)).val
        rw [special_comp_apply T1 T2 hComp, special_comp_apply T1 T2 hComp]
        have h := hReverse a b hab
        change SameRV (T2.toMap ((Map.comp (Map.inverse g hgf) U.inverseMap) a)).val
          (T2.toMap ((Map.comp (Map.inverse g hgf) U.inverseMap) b)).val at h
        rw [conjugate_tail_inverse T1 TB R0 U hsplit f hf a,
          conjugate_tail_inverse T1 TB R0 U hsplit f hf b] at h
        exact h

end IntegrationInACVF.Section5
