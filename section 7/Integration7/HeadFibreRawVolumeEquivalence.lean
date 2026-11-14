import Integration7.HeadFibreRawVolumePresentation
import Integration7.GammaEqualLabelEquivalenceGraphs
import Integration7.UnarySelectedNormalizationVolumeIso
import IntegrationSection6.RawContractionDomain

/-! The unnormalized unary contraction of a frozen head fibre is the
actual head-contracted RV fibre, retaining old selected coordinates first. -/

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
variable {B : Base (M := M)} {S : Set M} {n a k : ℕ}
variable {U : DefSet (M := M) S (n+1) a}

theorem head_fibre_raw_volume_equivalence {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (T : HeadPreparation U) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headAppendVolumeIndex T ρ) x) :
    let Z := headFibreRawVolumeObject hκ hs hreal hBS hU ρ hfin T hT hTarget x
    ∃ e : GammaRVIso P.toGamma.toGammaRVObject Z.toGammaRVObject,
      (∀ u, gammaVolumeValue Z.toGammaRVObject (e.equiv u) = gammaVolumeValue P.toGamma.toGammaRVObject u) ∧
      (∀ u, (e.equiv u).val = u.val) := by
  intro Z
  have hDom (r : Fin (1+T.arity) → RV (M := M)) :
      r ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ _ P.domain ↔
        r ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ _ (rvObjectDomain Z.object) :=
    (Set.ext_iff.mp P.domain_eq r).trans (head_fibre_raw_domain hκ hs hreal hBS hU ρ hfin T hT hTarget x r).symm
  let e : P.domain ≃ rvObjectDomain Z.object := {
    toFun := fun u => ⟨u.val,(hDom u.val).mp u.property⟩
    invFun := fun v => ⟨v.val,(hDom v.val).mpr v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcoord (u : P.domain) :
      gammaVolumeValue Z.toGammaRVObject (e u) = gammaVolumeValue P.toGamma.toGammaRVObject u := by
    have hP := (P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩
    exact (head_fibre_raw_volume hκ hs hreal hBS hU ρ hfin T hT hTarget x (e u)).trans hP.2.2
  let f : GammaRVIso P.toGamma.toGammaRVObject Z.toGammaRVObject :=
    FiniteRV.gammaIsoOfFiniteEquiv P.toGamma Z e
      (gamma_equal_label_equivalence_graph _ _ P.toGamma.domain_graph e (fun _ => rfl))
      (fun u => congrArg (fun t : Fin ((k+1)+1) → RV (M := M) => rawWeight (rvValues t)) (hcoord u).symm)
  exact ⟨f,hcoord,fun _ => rfl⟩

end IntegrationInACVF.Section7
