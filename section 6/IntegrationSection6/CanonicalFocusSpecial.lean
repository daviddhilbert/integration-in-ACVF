import IntegrationSection6.AdmissibleFocusExistence

/-! A canonical-focus-canonical chain has exactly one centripetal step,
with full original-Gamma certificates on every primitive. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

def canonicalFocusSpecial (A : DefSet (M := M) S n m) {i : Fin n} {k : Fin (n+m)}
    (D : Focus (canonicalImage A) i k) : SpecialBijection A (canonicalImage D.etaImage) where
  chain := .cons (.canonical A) (.cons (.centripetal D)
    (.cons (.canonical D.etaImage) (.nil _)))
  alternating := ⟨by decide,by decide,by decide,trivial⟩

@[simp] theorem canonicalFocusSpecial_length (A : DefSet (M := M) S n m)
    {i : Fin n} {k : Fin (n+m)} (D : Focus (canonicalImage A) i k) :
    (canonicalFocusSpecial A D).length = 1 := rfl

def gammaCanonicalFocusSpecial {B : Base (M := M)} (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S n m) {i : Fin n} {k : Fin (n+m)}
    (D : Focus (canonicalImage A) i k) (hA : GammaSetDefinable B (carrier A))
    (hD : GammaFocusDefinable B D) :
    GammaSpecialBijection B (carrier A) (carrier (canonicalImage D.etaImage)) where
  codes := S
  real_contains := hBS
  source := A
  target := canonicalImage D.etaImage
  source_eq := rfl
  target_eq := rfl
  special := canonicalFocusSpecial A D
  invariant_graphs := by
    let L := gammaLogicInput B
    have hC := GammaPrimitiveDefinable.target L (.canonical A) hA
    have hE := GammaPrimitiveDefinable.target L (.centripetal D) ⟨hC,hD⟩
    have hK := GammaPrimitiveDefinable.target L (.canonical D.etaImage) hE
    exact ⟨hA,⟨hC,hD⟩,hE,hK⟩

@[simp] theorem gammaCanonicalFocusSpecial_length {B : Base (M := M)} (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S n m) {i : Fin n} {k : Fin (n+m)}
    (D : Focus (canonicalImage A) i k) (hA : GammaSetDefinable B (carrier A))
    (hD : GammaFocusDefinable B D) :
    (gammaCanonicalFocusSpecial hBS A D hA hD).special.length = 1 := rfl

end IntegrationInACVF.Section6
