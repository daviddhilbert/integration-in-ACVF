module

public import Integration7.ContractionParameterExtension
public import Integration7.GammaEqualLabelEquivalenceGraphs
public import IntegrationSection6.RawSelectedContractions
public import IntegrationSection6.GammaSwappedVolumes

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Parameter enlargement leaves raw selected contraction labels and
all selected volume coordinates unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S R : Set M} {n a k : ℕ}

set_option maxHeartbeats 1600000 in
theorem raw_selected_contraction_extension_equivalence {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S) (hSR : S ⊆ R)
    (U : DefSet (M := M) S n a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program) :
    let Z := gammaSwapVolumeBlocks (FiniteRV.gammaRawSelectedContraction hκ hs hreal hBS hU ρ hfin T hT)
    let TD := T.extendBase hSR
    let W := gammaSwapVolumeBlocks (FiniteRV.gammaRawSelectedContraction hκ hs hreal (hBS.trans hSR) hU ρ hfin TD
      (T.program.extendBase_gamma hSR hT))
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
    change Fin.append (u.val ∘ TD.volumeIndex) (fun j => u.val (suffixIndex TD.program.rvArity_le (ρ j))) ∘
      (@finAddFlip k n) =
      Fin.append (u.val ∘ T.volumeIndex) (fun j => u.val (suffixIndex T.program.rvArity_le (ρ j))) ∘
      (@finAddFlip k n)
    have hindex : TD.volumeIndex = T.volumeIndex := funext (T.extendBase_volumeIndex hSR)
    rw [hindex]
  let f : GammaRVIso Z.toGammaRVObject W.toGammaRVObject :=
    FiniteRV.gammaIsoOfFiniteEquiv Z W e
      (gamma_equal_label_equivalence_graph _ _ Z.domain_graph e (fun _ => rfl))
      (fun u => congrArg (fun t : Fin (k+n) → RV (M := M) => rawWeight (rvValues t)) (hcoord u).symm)
  exact ⟨f,hcoord,fun _ => rfl⟩

end IntegrationInACVF.Section7
