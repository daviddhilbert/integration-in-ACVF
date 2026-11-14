import Integration7.RVAlmostEverywhereParameters

/-! A definable exceptional set has the same RV dimension after a
small parameter extension. Smallness of the containing context is stated
at the original cardinal, as required by parameter invariance. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a n : ℕ}

theorem rvDim_lt_of_small_extended_exception
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {S T : Set M} (hCT : S ⊆ T) (hS : Cardinal.mk S < C.κ) (hT : Cardinal.mk T < C.κ)
    (A : DefSet (rawRVSpace (M := M) a) S)
    (E : DefSet (rawRVSpace (M := M) a) T) (hAE : A.carrier ⊆ E.carrier)
    (hE : rvDim E < n) : rvDim A < n := by
  let hex := rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00
  have hi := rvDim_parameter_invariant hc hex C.uncountable.le C.saturated C.homogeneous
    hCT hS hT A
  rw [← hi]
  let f : Map (A.extend hCT) E := Map.inclusion hAE
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : E => z.val) h)
  exact (rvDim_le_of_finite_map f (Map.finiteFibres_of_injective hf)).trans_lt hE

end IntegrationInACVF.Section7
