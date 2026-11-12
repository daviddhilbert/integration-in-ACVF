import IntegrationSection6.UniformRootEquations
import IntegrationSection6.GammaRootFocus
import Section5.GammaRestriction

/-! The focus-existence part of6.12, with original Gamma parameters,
zero unchanged coordinates and a genuine special bijection of length one. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

/-- The labelled source may use any real presentation containing B.real;
its full source and focus graphs remain over B itself. -/
theorem exists_fullFocus_on_admissible_image {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (hBS : B.real ⊆ S) (A : DefSet (M := M) S n m)
    (hA : IsRVPullback (carrier A)) (hADef : GammaSetDefinable B (carrier A))
    (j : Fin n) (k : Fin m) (htag : Tagged (carrier A) j k)
    (C : Set (Fin n → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (hkeys : ∀ p ∈ carrier A, (fun i => (rv (p.1 i)).val) ∈ C)
    (hnz : ∀ t ∈ C, t j ≠ iRVZero)
    (halg : ∀ t : Fin n → CanonicalRV.RVSort M, rvValues t ∈ C →
      AlgebraicAtBase ⟨coordinateBase B.real j t,B.gamma⟩ .rv (t j).val) :
    ∃ D : Focus A j k, D.locus = carrier A ∧ GammaFocusDefinable B D := by
  obtain ⟨R,hR,hgood⟩ := exists_uniform_rootEquation hκ hs h00 B hsmall hB C hC j hnz halg
  have hcover : ∀ p ∈ carrier A, (fun i => (rv (p.1 i)).val) ∈
      @rootDomain M (@CanonicalStructure.normalize M sM) n R j :=
    fun p hp => hgood (hkeys p hp)
  exact ⟨rootFocus A R j k hcover (@Set.Definable.mono M B.real LRV (@CanonicalStructure.normalize M sM) (Fin n) S R hR hBS) hA htag,rfl,
    rootFocus_gamma hBS A R j k hR hcover hA htag hADef⟩

/-- A full-locus Gamma focus supplies the actual inherited length-one
chain, with every primitive and target Gamma graph certified. -/
def fullFocusSpecial {B : Base (M := M)} {A : DefSet (M := M) S n m}
    {j : Fin n} {k : Fin m} (hBS : B.real ⊆ S)
    (D : Focus A j k) (hA : GammaSetDefinable B (carrier A))
    (hD : GammaFocusDefinable B D) :
    GammaSpecialBijection B (carrier A) (carrier D.etaImage) where
  codes := S
  real_contains := hBS
  source := A
  target := D.etaImage
  source_eq := rfl
  target_eq := rfl
  special := SpecialBijection.centripetal D
  invariant_graphs := ⟨⟨hA,hD⟩,
    GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal D) ⟨hA,hD⟩⟩

@[simp] theorem fullFocusSpecial_length {B : Base (M := M)}
    {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m} (hBS : B.real ⊆ S)
    (D : Focus A j k) (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    (fullFocusSpecial hBS D hA hD).special.length = 1 := rfl

end IntegrationInACVF.Section6
