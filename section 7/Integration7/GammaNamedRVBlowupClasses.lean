import Integration7.GammaVolumeBlowupAddition
import Integration7.GammaVolumeIsomorphismClasses
import Integration7.GammaEssentialVolumeRestrictions
import Integration7.GammaRVTagMaps
import Integration7.GammaVolumeFullChartRestriction
import Integration7.VolumeCoproductUnits
import IntegrationSection6.FiniteGammaInitial

/-! Positive-degree RV volume classes over a Gamma base: actual volume
objects whose coordinate and density graphs are Gamma-definable over `B`,
coded over the real parameters of a context `C`, modulo common volume
blowups and isomorphisms with full Gamma graphs over `B`. Coproduct makes
them an additive commutative monoid. No relation between the common names
of `B` and `C.base` is assumed here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

theorem VolumeObjectGamma.empty (S : Set M) (k : ℕ) :
    VolumeObjectGamma (PositiveRVVolumeObject.empty S k) B := by
  constructor
  · apply GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph (B := B) _ _)
    intro p q
    constructor
    · exact False.elim
    · rintro ⟨u,_,_⟩
      exact u.property
  · apply GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph (B := B) _ _)
    intro p q
    constructor
    · exact False.elim
    · rintro ⟨u,_,_⟩
      exact u.property

def GammaVolumeObjects.empty (B : Base (M := M)) (S : Set M) (k : ℕ) : GammaVolumeObjects B S k :=
  ⟨PositiveRVVolumeObject.empty S k,VolumeObjectGamma.empty S k⟩

theorem gamma_volume_coprod_empty_embedding
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (hU : VolumeObjectGamma U B) :
    (volumeCoprodEmptyEmbedding hc C U).GammaDefinable B := by
  let E := PositiveRVVolumeObject.empty (M := M) (C.base : Set M) k
  have hF : RVMapGamma (rvCoprodLeftMap U.underlying.obj E.underlying.obj) B :=
    (gamma_rv_left_tag_map hc U.underlying.obj.domain E.underlying.obj.arity hU.domain_graph).congr
      (fun _ => rfl)
  exact gamma_volume_iso_of_full_map _ _
    (gamma_essential_volume_domain U hU.coordinates) hF (fun _ => rfl)

theorem gamma_volume_coprod_right_unit
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (hU : VolumeObjectGamma U B) :
    (volumeCoprodRightUnit hc C U).GammaDefinable B :=
  (gamma_volume_coprod_empty_embedding hc C hU).symm hc C B

theorem gamma_volume_coprod_left_unit
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (hU : VolumeObjectGamma U B) :
    (volumeCoprodLeftUnit hc C U).GammaDefinable B :=
  (gamma_volume_coprod_swap hc C (VolumeObjectGamma.empty _ k) hU).trans hc C B
    (gamma_volume_coprod_right_unit hc C hU)

def gammaVolumeBlowupSetoid (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) (k : ℕ) :
    Setoid (GammaVolumeObjects B (C.base : Set M) k) where
  r := GammaVolumeBlowupEquivalent B (C.base : Set M) k
  iseqv := ⟨GammaVolumeBlowupEquivalent.refl hc C B,
    GammaVolumeBlowupEquivalent.symm hc C B,GammaVolumeBlowupEquivalent.trans hc C B⟩

/-- Positive-degree (`k+1` RV coordinates) volume classes over the Gamma base `B`,
coded over `C.base`. -/
abbrev GammaVolumeBlowupClasses (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) (k : ℕ) := Quotient (gammaVolumeBlowupSetoid hc C B k)

def gammaVolumeBlowupClass (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) {k : ℕ}
    (U : GammaVolumeObjects B (C.base : Set M) k) : GammaVolumeBlowupClasses hc C B k :=
  Quotient.mk _ U

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (B : Base (M := M))

theorem gammaVolumeBlowupClass_eq_iff {U V : GammaVolumeObjects B (C.base : Set M) k} :
    gammaVolumeBlowupClass hc C B U = gammaVolumeBlowupClass hc C B V ↔
      GammaVolumeBlowupEquivalent B (C.base : Set M) k U V :=
  ⟨fun h => Quotient.exact h,fun h => Quotient.sound (s := gammaVolumeBlowupSetoid hc C B k) h⟩

theorem gammaVolumeBlowupClass_iso {U V : GammaVolumeObjects B (C.base : Set M) k}
    (e : RVVolumeIso U.val V.val) (he : e.GammaDefinable B) :
    gammaVolumeBlowupClass hc C B U = gammaVolumeBlowupClass hc C B V :=
  Quotient.sound (s := gammaVolumeBlowupSetoid hc C B k) (.of_iso C B e he)

theorem gammaVolumeBlowupClass_blowup {U V : GammaVolumeObjects B (C.base : Set M) k}
    (b : VolumeBlowup U.val V.val) (hb : b.GammaDefinable B) :
    gammaVolumeBlowupClass hc C B U = gammaVolumeBlowupClass hc C B V :=
  Quotient.sound (s := gammaVolumeBlowupSetoid hc C B k) (.of_blowup hc C B b hb)

instance gammaVolumeBlowupClassesAdd (k : ℕ) : Add (GammaVolumeBlowupClasses hc C B k) :=
  ⟨Quotient.map₂ GammaVolumeObjects.coprod (fun _ _ h _ _ g =>
    GammaVolumeBlowupEquivalent.coprod hc C h g)⟩

instance gammaVolumeBlowupClassesZero (k : ℕ) : Zero (GammaVolumeBlowupClasses hc C B k) :=
  ⟨gammaVolumeBlowupClass hc C B (GammaVolumeObjects.empty B (C.base : Set M) k)⟩

instance gammaVolumeBlowupClassesAddCommMonoid (k : ℕ) :
    AddCommMonoid (GammaVolumeBlowupClasses hc C B k) where
  add_assoc a b c := Quotient.inductionOn₃ a b c (fun U V W =>
    gammaVolumeBlowupClass_iso hc C B (volumeCoprodAssoc hc C U.val V.val W.val)
      (gamma_volume_coprod_assoc hc C U.property V.property W.property))
  add_comm a b := Quotient.inductionOn₂ a b (fun U V =>
    gammaVolumeBlowupClass_iso hc C B (volumeCoprodSwap hc C U.val V.val)
      (gamma_volume_coprod_swap hc C U.property V.property))
  zero_add a := Quotient.inductionOn a (fun U =>
    gammaVolumeBlowupClass_iso hc C B (volumeCoprodLeftUnit hc C U.val)
      (gamma_volume_coprod_left_unit hc C U.property))
  add_zero a := Quotient.inductionOn a (fun U =>
    gammaVolumeBlowupClass_iso hc C B (volumeCoprodRightUnit hc C U.val)
      (gamma_volume_coprod_right_unit hc C U.property))
  nsmul := nsmulRec

@[simp] theorem gammaVolumeBlowupClass_coprod (U V : GammaVolumeObjects B (C.base : Set M) k) :
    gammaVolumeBlowupClass hc C B (U.coprod V) =
      gammaVolumeBlowupClass hc C B U + gammaVolumeBlowupClass hc C B V := rfl

@[simp] theorem gammaVolumeBlowupClass_empty (k : ℕ) :
    gammaVolumeBlowupClass hc C B (GammaVolumeObjects.empty B (C.base : Set M) k) = 0 := rfl

end IntegrationInACVF.Section7
