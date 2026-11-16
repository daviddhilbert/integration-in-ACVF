module

public import Integration7.HKPointIsomorphismCodes

@[expose] public section

/-! Changing equal fibre carrier presentations retains the literal
equation between the two density labels. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m a b : ℕ}

theorem weighted_point_iso_congr_density
    {A A' : Set (Point (M := M) n a)} {D D' : Set (Point (M := M) m b)}
    (e : GammaIso B A D) (hA : A = A') (hD : D = D') (δ : Fin a) (ε : Fin b)
    (he : ∀ u, u.val.2 δ = (e.equiv u).val.2 ε) :
    ∀ u, u.val.2 δ = ((e.congr hA hD).equiv u).val.2 ε := by
  cases hA
  cases hD
  exact he

end IntegrationInACVF.Section7.HK
