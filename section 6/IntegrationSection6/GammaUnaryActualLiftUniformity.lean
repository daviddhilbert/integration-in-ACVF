import IntegrationSection6.GammaUnaryFamilyLiftUniformity
import IntegrationSection6.GammaSelectedLabelFibrePresentations

/-! Lemma6.14 for one VF coordinate, stated directly for the actual RV[k]
fibres of mixed sets and arbitrary unary standard contractions. -/
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
variable {B : Base (M := M)} {R : Set M} {a b k : ℕ}

theorem gamma_unary_actual_lift_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : DefSet (M := M) R 1 a) (V : DefSet (M := M) R 1 b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hfinU : ∀ (x : Fin 1 → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin 1 → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    (hCommon : ∀ x : Fin 1 → VF (M := M),
      ∀ P : SelectedLabelFibrePresentation B U ρ x, ∀ Q : SelectedLabelFibrePresentation B V τ x,
      GammaIsp hκ.le hs h00 (small_union_range hκ.le B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma)
    (Z W : GammaRVFiniteObject B (k+1))
    (hZ : ∀ t : Fin k → RV (M := M),
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity Z.object) 1 ((gammaVolumeSliceSchema Z).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema Z).rowVolume (fun j => (t j).val)),
      Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (carrier U ∩ {q | q.2 ∘ ρ = t}) P.toGamma.lift))
    (hW : ∀ t : Fin k → RV (M := M),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity W.object) 1 ((gammaVolumeSliceSchema W).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema W).rowVolume (fun j => (t j).val)),
      Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (carrier V ∩ {q | q.2 ∘ τ = t}) Q.toGamma.lift)) :
    GammaIsp hκ.le hs h00 hreal Z W := by
  let A := PresentedSet.univ (pointSpace (M := M) 1 0) B.real
  have hA : GammaSetDefinable B (carrier A) := (gammaLogicInput B).real_set _ (setDefinable A)
  let F := gammaSelectedLabelSchema U hU ρ
  let G := gammaSelectedLabelSchema V hV τ
  apply gamma_unary_family_lift_uniformity hκ hs h00 hreal hgamma δ hδ hδ1
    A hA F G ρ τ
    (fun x => gammaSelectedLabelSchema_finiteRows U hU ρ hfinU x.val.1)
    (fun x => gammaSelectedLabelSchema_finiteRows V hV τ hfinV x.val.1)
    (fun x => gammaSelectedLabelSchema_labels U hU ρ x.val)
    (fun x => gammaSelectedLabelSchema_labels V hV τ x.val) ?_
    Z W ?_ ?_
  · intro x P Q
    have h := hCommon x.val.1 (selectedLabelFibreOfSchema U hU ρ x.val.1 P)
      (selectedLabelFibreOfSchema V hV τ x.val.1 Q)
    simpa only [selectedLabelFibreOfSchema_toGamma] using h
  · intro t P
    obtain ⟨f⟩ := hZ t P
    exact ⟨f.congr (congrArg (fun D : Set (Point (M := M) 1 a) => D ∩ {q | q.2 ∘ ρ = t}) (gammaSelectedLabelSchema_source U hU ρ)) rfl⟩
  · intro t Q
    obtain ⟨f⟩ := hW t Q
    exact ⟨f.congr (congrArg (fun D : Set (Point (M := M) 1 b) => D ∩ {q | q.2 ∘ τ = t}) (gammaSelectedLabelSchema_source V hV τ)) rfl⟩

end IntegrationInACVF.Section6.FiniteRV
