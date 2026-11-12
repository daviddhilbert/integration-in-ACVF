import IntegrationSection6.ContractionPresentationLabels
import IntegrationSection6.OrderedSelectedWeights
import IntegrationSection6.FiniteSelectedContractions
import IntegrationSection6.GammaDegreeTransport

/-! The recursive finite presentation of an actual standard contraction
is isomorphic in RV[n+k] to its first-volume selected-label presentation.
The proof compares weights and the complete original-Gamma label graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m k : ℕ}
variable {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

def gammaContractionPresentationIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin k → Fin m)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program)
    (P : GammaSelectedRVPresentation B C.target (orderedSelectedIndex C.program ρ)) :
    GammaRVIso P.toGamma.toGammaRVObject
      (gammaCastDegree (orderedVolumeDegree_eq n k).symm
        (gammaFiniteSelectedContraction hκ hs hreal hBS hA ρ hfin C hC)).toGammaRVObject := by
  let Q := gammaFiniteSelectedContraction hκ hs hreal hBS hA ρ hfin C hC
  let e := normalizedContractionPresentationEquiv C (orderedSelectedIndex C.program ρ) P
  apply gammaIsoOfEqualDegreeEquiv (orderedVolumeDegree_eq n k) P.toGamma Q e
  · let G := rvCoordinatePointMap (prependVolumeIndex C.volumeIndex) B.real
    apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph P.domain_graph
      ((gammaLogicInput B).real_map_graph G))
    intro p q
    constructor
    · rintro ⟨hp,a,ha,hq⟩
      let u : P.domain := ⟨p.2,(Set.ext_iff.mp P.domain_eq p.2).mpr hp⟩
      refine ⟨u,rfl,?_⟩
      have he := normalizedContractionPresentationEquiv_value C (orderedSelectedIndex C.program ρ) P u
      exact he.trans ((congrArg (fun r => r ∘ prependVolumeIndex C.volumeIndex) (congrArg Prod.snd ha)).symm.trans
        (congrArg Prod.snd hq))
    · rintro ⟨u,hu,hq⟩
      have hp := hu ▸ (Set.ext_iff.mp P.domain_eq u.val).mp u.property
      refine ⟨hp,⟨p,Set.mem_univ _⟩,rfl,Prod.ext (Subsingleton.elim _ _) ?_⟩
      have he := normalizedContractionPresentationEquiv_value C (orderedSelectedIndex C.program ρ) P u
      exact (congrArg (fun r => r ∘ prependVolumeIndex C.volumeIndex) hu).symm.trans (he.symm.trans hq)
  · intro u
    have hP : (P.volume u).val = u.val ∘ orderedSelectedIndex C.program ρ :=
      ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2.2.symm
    have hQ : gammaVolumeValue Q.toGammaRVObject (e u) =
        Fin.append (u.val ∘ C.volumeIndex) (fun j => u.val (suffixIndex C.program.rvArity_le (ρ j))) := by
      change Fin.append (rvObjectVolume C.normalizedObject (e u)).val
        ((e u).val ∘ (fun j => contractionOldLabelIndex C (ρ j))) = _
      apply congrArg₂ Fin.append
      · change (rvObjectVolume C.normalizedObject
          (toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex
            (contractionPresentationLabelEquiv C (orderedSelectedIndex C.program ρ) P u))).val = _
        exact toFirstVolume_volume _ _ _
      · funext j
        rw [normalizedContractionPresentationEquiv_value]
        change u.val (prependVolumeIndex C.volumeIndex (Fin.natAdd n _)) = _
        rw [prependVolumeIndex,Fin.addCases_right]
        rfl
    change rawWeight (fun j => ((P.volume u).val j).val) = rawWeight (fun j => (gammaVolumeValue Q.toGammaRVObject (e u) j).val)
    rw [hP,hQ]
    have hApp : (fun j => (Fin.append (u.val ∘ C.volumeIndex)
        (fun j => u.val (suffixIndex C.program.rvArity_le (ρ j))) j).val) =
        Fin.append (fun i => (u.val (C.volumeIndex i)).val)
          (fun j => (u.val (suffixIndex C.program.rvArity_le (ρ j))).val) := by
      funext j
      cases j using Fin.addCases <;> simp only [Fin.append_left,Fin.append_right,Function.comp_apply]
    rw [hApp,rawWeight_append]
    apply (orderedSelectedIndex_weight C.program ρ u.val).trans
    congr 1
    unfold rawWeight
    exact (Fintype.sum_equiv σ.symm _ _ (fun j => rfl)).symm

end IntegrationInACVF.Section6.FiniteRV
