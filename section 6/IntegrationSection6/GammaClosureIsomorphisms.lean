import IntegrationSection6.GammaDefinableBaseReduction
import Section5.GammaLift

/-! Descend full isomorphism graphs from dcl(B) to the original base B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def closureBaseReduction (B : Base (M := M)) : GammaDefinableBaseReduction (closureBase B) B where
  real_subset := (subset_closureBase B).1
  real_definable := by
    rintro c ⟨τ,hc⟩ σ hσ
    have he : τ = σ := CanonicalStructure.sort_unique hM (hc.proper c (Set.mem_singleton _)) hσ
    cases he
    exact hc
  gamma_definable := fun _ h => h

def gammaIsoClosureDescend {B : Base (M := M)} {n m u v : ℕ}
    {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) u v)}
    (e : GammaIso (closureBase B) A C) : GammaIso B A C :=
  ⟨e.equiv,(closureBaseReduction B).definable e.graph⟩

end IntegrationInACVF.Section6
