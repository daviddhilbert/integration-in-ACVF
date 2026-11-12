import IntegrationSection6.GammaDefinableBaseReduction
import Section5.GammaRestriction

/-! Definable-name elimination preserves the full Gamma source, focus,
scalar and graph certificates of actual special chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {S : Set M} {p a b : ℕ}

theorem GammaDefinableBaseReduction.focusDefinable (H : GammaDefinableBaseReduction C B)
    {A : DefSet (M := M) S p a} {i : Fin p} {j : Fin a} (D : Focus A i j)
    (hD : GammaFocusDefinable C D) : GammaFocusDefinable B D :=
  ⟨H.definable hD.1,H.definable hD.2⟩

theorem GammaDefinableBaseReduction.chainDefinable (H : GammaDefinableBaseReduction C B)
    {A : DefSet (M := M) S p a} {D : DefSet (M := M) S p b} (T : Chain S p A D)
    (hT : GammaChainDefinable C T) : GammaChainDefinable B T := by
  induction T with
  | nil A => exact H.definable hT
  | cons f tail ih =>
    refine ⟨?_,ih hT.2⟩
    cases f with
    | canonical A => exact H.definable hT.1
    | centripetal D => exact ⟨H.definable hT.1.1,H.focusDefinable D hT.1.2⟩

end IntegrationInACVF.Section6
