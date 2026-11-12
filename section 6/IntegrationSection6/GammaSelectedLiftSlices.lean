import IntegrationSection6.GammaVolumeSliceLiftCarriers
import IntegrationSection6.GammaSwappedVolumes
import IntegrationSection6.GammaNamedRVFibres
import IntegrationSection6.FiniteGammaLiftGluing

/-! A selected-volume slice has exactly the original lift with those old
RV labels fixed. The label-identity comparison keeps the full Gamma graph
over the original base and the selected named RV tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n e : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaSelectedSlicePresentation_lift (U : GammaRVObject B n)
    (ρ : Fin e → Fin (rvObjectArity U.object))
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin (rvObjectArity U.object) → RV (M := M) | (x,r) ∈ U.lift ∧ r ∘ ρ = t}.Finite)
    (t : Fin e → RV (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (rvObjectArity U.object) n
      ((gammaVolumeSliceSchema (gammaPrependSelectedVolume U ρ hfin)).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaPrependSelectedVolume U ρ hfin)).rowVolume (fun j => (t j).val))) :
    P.toGamma.lift = U.lift ∩ {p | p.2 ∘ ρ = t} := by
  apply (gammaVolumeSlicePresentation_lift (gammaPrependSelectedVolume U ρ hfin) t P).trans
  apply Set.ext
  intro p
  change (∃ u : rvObjectDomain U.object, u.val = p.2 ∧
    gammaVolumeValue (gammaPrependSelectedVolume U ρ hfin).toGammaRVObject u = Fin.append t (@tupleRV M N hN n p.1)) ↔ _
  constructor
  · rintro ⟨u,hu,hv⟩
    rw [gammaPrependSelectedVolume_value] at hv
    have hHead : u.val ∘ ρ = t := funext (fun j => by
      simpa only [Fin.append_left] using congrFun hv (Fin.castAdd n j))
    have hTail : gammaVolumeValue U u = @tupleRV M N hN n p.1 := funext (fun j => by
      simpa only [Fin.append_right] using congrFun hv (Fin.natAdd e j))
    exact ⟨⟨u,hu,hTail⟩,(congrArg (fun v => v ∘ ρ) hu).symm.trans hHead⟩
  · rintro ⟨⟨u,hu,hv⟩,ht⟩
    refine ⟨u,hu,?_⟩
    rw [gammaPrependSelectedVolume_value]
    exact congrArg₂ Fin.append ((congrArg (fun v => v ∘ ρ) hu).trans ht) hv

def gammaSelectedSliceLiftIso (U : GammaRVObject B n)
    (ρ : Fin e → Fin (rvObjectArity U.object))
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin (rvObjectArity U.object) → RV (M := M) | (x,r) ∈ U.lift ∧ r ∘ ρ = t}.Finite)
    (t : Fin e → RV (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (rvObjectArity U.object) n
      ((gammaVolumeSliceSchema (gammaPrependSelectedVolume U ρ hfin)).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaPrependSelectedVolume U ρ hfin)).rowVolume (fun j => (t j).val))) :
    GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (U.lift ∩ {p | p.2 ∘ ρ = t}) P.toGamma.lift := by
  let Bt : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
  have hU : GammaSetDefinable Bt U.lift := U.lift_definable.mono Set.subset_union_left (Set.Subset.refl _)
  have hD := (gammaLogicInput Bt).inter hU (gamma_named_rv_label_fibre ρ t)
  exact (gammaIso_reflexive _ hD).congr rfl (gammaSelectedSlicePresentation_lift U ρ hfin t P).symm

end IntegrationInACVF.Section6
