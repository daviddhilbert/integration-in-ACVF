import IntegrationSection6.FiniteGammaScissorRestrictions
import IntegrationSection6.FiniteGammaInitial

/-! Actual generators of the inherited original-Gamma finite-volume
Grothendieck presentation, with its actual isomorphism and empty relations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

def gammaFiniteScissorObject (U : GammaRVFiniteObject B k) :
    {x : GammaRVObject B k // GammaRVFiniteVolumes x} := ⟨U.toGammaRVObject,U.finite_volume⟩

def gammaFiniteScissorClass (U : GammaRVFiniteObject B k) : KPlus (gammaRVFinitePresentation B k) :=
  of (gammaRVFinitePresentation B k) (gammaFiniteScissorObject U)

theorem gammaFiniteScissorClass_iso {U V : GammaRVFiniteObject B k}
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    gammaFiniteScissorClass U = gammaFiniteScissorClass V :=
  of_iso (gammaRVFinitePresentation B k) ⟨e⟩

theorem gammaFiniteScissorClass_empty (U : GammaRVFiniteObject B k)
    (hU : ∀ u : rvObjectDomain U.object, False) : gammaFiniteScissorClass U = 0 := by
  let P := gammaRVFinitePresentation B k
  let V : GammaRVFiniteObject B k := { toGammaRVObject := P.empty.val, finite_volume := P.empty.property }
  have hV : ∀ v : rvObjectDomain V.object, False := fun v => v.property
  letI : IsEmpty (rvObjectDomain U.object) := ⟨hU⟩
  letI : IsEmpty (rvObjectDomain V.object) := ⟨hV⟩
  let e : rvObjectDomain U.object ≃ rvObjectDomain V.object := Equiv.equivOfIsEmpty _ _
  have he : GammaGraphDefinable B (gammaRVLabelGraph U.toGammaRVObject V.toGammaRVObject e) := by
    apply GammaGraphDefinable.congr (gamma_empty_graph (B := B) (rvObjectArity U.object) (rvObjectArity V.object))
    intro p q
    constructor
    · intro h; exact h.elim
    · rintro ⟨u,_,_⟩; exact hU u
  have E := gammaIsoOfFiniteEquiv U V e he (fun u => (hU u).elim)
  exact (gammaFiniteScissorClass_iso E).trans (of_empty P)

end IntegrationInACVF.Section6.FiniteRV
