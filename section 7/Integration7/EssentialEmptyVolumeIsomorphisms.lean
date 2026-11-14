import Integration7.EssentialVolumeRestriction
import Integration7.IndexedVolumeEmpty
import Integration7.GammaIndexedVolumeEmpty

/-! Objects with empty essential domains have their actual empty volume
isomorphism, even when the full label domains contain degenerate points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

def RVVolumeIso.of_essential_empty
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : U.essential.obj.domain.carrier = ∅) (hV : V.essential.obj.domain.carrier = ∅) :
    RVVolumeIso U V :=
  (((essentialCoreIso hc C U).symm hc C).trans hc C
    (RVVolumeIso.of_empty hc C U.essentialCore V.essentialCore hU hV)).trans hc C (essentialCoreIso hc C V)

theorem gamma_volume_iso_of_essential_empty
    {U V : PositiveRVVolumeObject (M := M) S k} (e : RVVolumeIso U V)
    (hU : U.essential.obj.domain.carrier = ∅) : e.GammaDefinable B := by
  apply GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph U.underlying.obj.arity V.underlying.obj.arity)
  intro p q
  constructor
  · exact False.elim
  · rintro ⟨u,_,_⟩
    exact hU.le u.property

end IntegrationInACVF.Section7
