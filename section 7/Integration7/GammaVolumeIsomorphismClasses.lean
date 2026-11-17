module

public import Integration7.GammaVolumeCoproductCoherence
public import Integration7.GammaVolumeIsoGraphOperations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Isomorphism classes of the existing actual Gamma volume objects.
The relation requires a full original-Gamma volume chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev GammaVolumeObjects (B : Base (M := M)) (S : Set M) (k : ℕ) :=
  {U : PositiveRVVolumeObject (M := M) S k // VolumeObjectGamma U B}

def gammaVolumeIsoSetoid (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) (k : ℕ) :
    Setoid (GammaVolumeObjects B (C.base : Set M) k) where
  r U V := ∃ e : RVVolumeIso U.val V.val, e.GammaDefinable B
  iseqv := ⟨fun U => ⟨RVVolumeIso.refl hc C U.val,U.property.identity_iso hc C⟩,
    fun ⟨e,he⟩ => ⟨e.symm hc C,he.symm hc C B⟩,
    fun ⟨e,he⟩ ⟨f,hf⟩ => ⟨e.trans hc C f,he.trans hc C B hf⟩⟩

abbrev GammaVolumeIsoClasses (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) (k : ℕ) := Quotient (gammaVolumeIsoSetoid hc C B k)

def gammaVolumeIsoClass (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) {k : ℕ}
    (U : GammaVolumeObjects B (C.base : Set M) k) : GammaVolumeIsoClasses hc C B k := Quotient.mk _ U

theorem gammaVolumeIsoClass_eq_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) {k : ℕ}
    {U V : GammaVolumeObjects B (C.base : Set M) k} :
    gammaVolumeIsoClass hc C B U = gammaVolumeIsoClass hc C B V ↔
      ∃ e : RVVolumeIso U.val V.val, e.GammaDefinable B :=
  ⟨fun h => Quotient.exact h,fun h => Quotient.sound (s := gammaVolumeIsoSetoid hc C B k) h⟩

theorem gammaVolumeIsoClass_iso (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) {k : ℕ}
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (e : RVVolumeIso U.val V.val) (he : e.GammaDefinable B) :
    gammaVolumeIsoClass hc C B U = gammaVolumeIsoClass hc C B V := Quotient.sound ⟨e,he⟩

end IntegrationInACVF.Section7
