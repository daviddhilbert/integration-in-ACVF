module

public import Integration7.ContractionParameterExtension
public import Integration7.GammaEqualLabelEquivalenceGraphs
public import IntegrationSection6.RawFiniteContractions

@[expose] public section

/-! Enlarging the containing real presentation base leaves every raw
finite contraction label and its entire VF-tag tuple unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S R : Set M} {n a : ℕ}

theorem raw_finite_contraction_extension_equivalence {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S) (hSR : S ⊆ R)
    (U : DefSet (M := M) S n a) (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program) :
    let Z := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBS hU hfin T hT
    let TD := T.extendBase hSR
    let W := FiniteRV.gammaRawFiniteContraction hκ hs hreal (hBS.trans hSR) hU hfin TD
      (T.program.extendBase_gamma hSR hT)
    ∃ e : GammaRVIso Z.toGammaRVObject W.toGammaRVObject,
      (∀ u, gammaVolumeValue W.toGammaRVObject (e.equiv u) = gammaVolumeValue Z.toGammaRVObject u) ∧
      (∀ u, (e.equiv u).val = u.val) := by
  intro Z TD W
  let e : rvObjectDomain Z.object ≃ rvObjectDomain W.object := {
    toFun := fun u => ⟨u.val,u.property⟩
    invFun := fun v => ⟨v.val,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcoord (u : rvObjectDomain Z.object) :
      gammaVolumeValue W.toGammaRVObject (e u) = gammaVolumeValue Z.toGammaRVObject u := by
    change u.val ∘ TD.volumeIndex = u.val ∘ T.volumeIndex
    funext i
    exact congrArg u.val (T.extendBase_volumeIndex hSR i)
  let f := FiniteRV.gammaIsoOfFiniteEquiv Z W e
    (gamma_equal_label_equivalence_graph _ _ Z.domain_graph e (fun _ => rfl))
    (fun u => congrArg (fun t : Fin n → RV (M := M) => rawWeight (rvValues t)) (hcoord u).symm)
  exact ⟨f,hcoord,fun _ => rfl⟩

end IntegrationInACVF.Section7
