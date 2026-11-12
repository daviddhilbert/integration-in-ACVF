import IntegrationSection6.PartialFocusBlowup
import IntegrationSection6.CanonicalPullbackPresentation
import IntegrationSection6.NormalizedCanonicalLifts

/-! Corollary6.10 for actual alternating special-bijection chains. Each
centripetal step replaces its genuine active locus; canonical steps have
length zero and contribute only a volume-preserving RV presentation change. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def chainPrimitiveCount {m l : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l} : Chain S n A C → ℕ
  | .nil _ => 0
  | .cons _ tail => chainPrimitiveCount tail + 1

theorem chainAlternating_none {m l : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l} {T : Chain S n A C}
    {previous : Option Bool} (h : T.Alternating previous) : T.Alternating none := by
  cases T with
  | nil => trivial
  | cons p tail =>
    cases p <;> exact ⟨by decide,h.2⟩

theorem specialChain_blowup_pair {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {m l : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l} (T : Chain S n A C) :
    (∀ (V : @SpecialTransformations.DefinableGeometry.DefSet LRV M N
          (@SpecialTransformations.Section4.rawRVSpace M N m) S)
       (v : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S V
          (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
            (@SpecialTransformations.Section4.rawRVSpace M N n) S)),
      @PresentsLift M N hN S n (@RVObject.mk M N S n m V v) (normalizedPointSet A) →
      T.Alternating none →
      @IteratedBlowup M N hN S n T.length (@RVObject.mk M N S n m V v)
        (@pullbackObject M sM hM S n l C)) ∧
    (IsRVPullback (carrier A) → T.Alternating (some true) →
      @IteratedBlowup M N hN S n T.length (@pullbackObject M sM hM S n m A)
        (@pullbackObject M sM hM S n l C)) := by
  induction T with
  | nil A =>
    constructor
    · intro V v h _
      let e := pullbackPresentationIso h
      letI := N
      letI := hN
      exact .zero ⟨e.symm⟩
    · intro _ _
      letI := N
      letI := hN
      exact .refl _
  | @cons m l k A B C p tail ih =>
    cases p with
    | canonical A =>
      constructor
      · intro V v h hT
        let U := @RVObject.mk M N S n m V v
        have hR := normalizedPresentsLift_canonical h
        let R := @canonicalRVKeyObject M N S n U
        let e := @canonicalRVKeyIso M N hN S n U
        have hAlt := chainAlternating_none hT.2
        have ht := ih.1 (@RVObject.domain M N S n R) (@RVObject.volume M N S n R) hR hAlt
        letI := N
        letI := hN
        simpa only [Chain.length,Primitive.length,zero_add] using ht.sourceIso e
      · intro hA hT
        have hR := normalizedCanonicalImage_presents A hA
        let R := @pullbackObject M sM hM S n m A
        have hAlt := chainAlternating_none hT.2
        have ht := ih.1 (@RVObject.domain M N S n R) (@RVObject.volume M N S n R) hR hAlt
        have hRe : @RVObject.mk M N S n (n+m) (@RVObject.domain M N S n R)
            (@RVObject.volume M N S n R) = R := rfl
        rw [hRe] at ht
        letI := N
        letI := hN
        simpa only [Chain.length,Primitive.length,zero_add] using ht
    | centripetal D =>
      constructor
      · intro V v h hT
        let E := partialFocusBlowup h D hκ hs hsmall
        have hA := (pullback_normalize (carrier A)).mp
          (@PresentsLift.pullback M N hN S n (@RVObject.mk M N S n m V v) (normalizedPointSet A) h)
        have ht := ih.2 (D.etaImage_pullback hA) hT.2
        letI := N
        letI := hN
        simpa only [Chain.length,Primitive.length] using (IteratedBlowup.single E).trans ht
      · intro _ hT
        exact False.elim (hT.1 rfl)


theorem specialChain_blowup {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    {l : ℕ} {C : SpecialTransformations.Section5.DefSet (M := M) S n l}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    (T : Chain S n A C) (hT : T.Alternating none) :
    @IteratedBlowup M N hN S n T.length U (@pullbackObject M sM hM S n l C) := by
  cases U with
  | mk m V v => exact (specialChain_blowup_pair hκ hs hsmall T).1 V v h hT

theorem corollary_6_10 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U : @RVObject M N S n) {l : ℕ}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l}
    (T : SpecialBijection (typedLift U) C) :
    @IteratedBlowup M N hN S n T.length U (@pullbackObject M sM hM S n l C) :=
  specialChain_blowup hκ hs hsmall (normalizedTypedLift_presents U) T.chain T.alternating

end IntegrationInACVF.Section6
