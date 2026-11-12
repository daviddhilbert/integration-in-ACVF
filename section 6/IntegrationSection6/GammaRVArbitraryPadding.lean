import IntegrationSection6.GammaLiftPadding
import IntegrationSection6.GammaNonzeroResolutions

/-! Zero-volume padding through any finite number of degrees preserves
both the literal lifted object up to Gamma isomorphism and its nonzero
resolution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {i j : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

def gammaRaiseRVToAt (hij : i ≤ j) (U : GammaObjectAt B Set.univ i) : GammaObjectAt B Set.univ j :=
  Nat.leRecOn hij (fun V => gammaPadAt V) U

theorem gammaRaiseRVToAt_refl (U : GammaObjectAt B Set.univ i) : gammaRaiseRVToAt (Nat.le_refl i) U = U :=
  Nat.leRecOn_self U

theorem gammaRaiseRVToAt_succ (hij : i ≤ j) (U : GammaObjectAt B Set.univ i) :
    gammaRaiseRVToAt (hij.trans (Nat.le_succ j)) U = gammaPadAt (gammaRaiseRVToAt hij U) :=
  Nat.leRecOn_succ hij U

theorem gammaRaiseRVToAt_resolution (hij : i ≤ j) (U : GammaObjectAt B Set.univ i) :
    gammaNonzeroResolutionAt j (gammaIsoClassAt (gammaRaiseRVToAt hij U)) =
      gammaNonzeroResolutionAt i (gammaIsoClassAt U) := by
  induction j,hij using Nat.le_induction with
  | base => rw [gammaRaiseRVToAt_refl]
  | succ j hij ih => rw [gammaRaiseRVToAt_succ hij,← gammaPaddingClassesAt_class,gammaNonzeroResolutionAt_padding,ih]

theorem gammaRaiseRVToAt_lift (hij : i ≤ j) (U : GammaObjectAt B Set.univ i) :
    Nonempty (GammaIso B U.toGamma.lift (gammaRaiseRVToAt hij U).toGamma.lift) := by
  induction j,hij using Nat.le_induction with
  | base =>
    rw [gammaRaiseRVToAt_refl]
    exact ⟨gammaIso_reflexive U.toGamma.lift U.toGamma.toGammaRVObject.lift_definable⟩
  | succ j hij ih =>
    rw [gammaRaiseRVToAt_succ hij]
    obtain ⟨e⟩ := ih
    exact ⟨e.trans (gammaLogicInput B) (gammaLiftPaddingIsoAt (gammaRaiseRVToAt hij U))⟩

end IntegrationInACVF.Section6.FiniteRV
