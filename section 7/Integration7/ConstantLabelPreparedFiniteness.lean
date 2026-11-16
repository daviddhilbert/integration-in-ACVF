module

public import Integration7.ConstantLabelPreparedRVProjections
public import Integration7.BalancedUnaryVolumePreparation

@[expose] public section

/-! Constant carried labels give finite RV fibres of the actual source;
Gamma special bijectivity then proves finite volume of the actual target
pullback object. No finiteness conclusion is assumed as new input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b l : ℕ}
variable {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {t : Fin l → RV (M := M)}

theorem constant_label_prepared_pullback_finite_volume {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (L : ConstantRVLabelSpecialPreparation T H t P) :
    @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ S _ _ (rvObjectVolume (pullbackObject L.target)) := by
  apply gamma_special_pullback_finite_volume hκ hs hsmall L.special L.gamma L.pullback
  intro x
  apply (Set.finite_singleton t).subset
  intro z hz
  exact Set.mem_singleton_iff.mpr (L.source_labels ⟨(x,z),hz⟩)

end IntegrationInACVF.Section7
