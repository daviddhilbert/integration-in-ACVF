import IntegrationSection6.GammaPreparedSelectedSliceIsomorphisms
import IntegrationSection6.FiniteSelectedContractionSlices
import IntegrationSection6.GammaVolumeSliceUniformity

/-! Compare an arbitrary unary standard contraction with a prepared
indexed family object, using actual slice lift isomorphisms and unary
common-blowup uniformity over the selected RV values. -/
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
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S R : Set M} {l a k : ℕ}
variable {A : Set (Point (M := M) 1 0)}
open FiniteRV

theorem gamma_unary_prepared_contraction_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (C : DefSet (M := M) S 1 l) (e : GammaIso B A (carrier C))
    (hA : GammaSetDefinable B A) (hC : IsRVPullback (carrier C))
    (F : GammaFiniteRVSchema B 1 a k) (G : GammaFiniteRVSchema B (1+l) a k (fun _ => .rv))
    (ρ : Fin k → Fin a)
    (hRows : ∀ c : C, GammaSchemaRowAgreement F (rawVFParameter (e.equiv.symm c).val) G (rawPreparedKey c.val))
    (BP : PreparedIndexPresentation B C)
    (hG : ∀ s ∈ preparedKeyDomain C, G.finiteRow (fun j => (s j).val))
    (hLabels : ∀ s ∈ preparedKeyDomain C, ∀ r y, G.rowVolume (fun j => (s j).val) r y ↔
      r ∈ G.rowDomain (fun j => (s j).val) ∧ r ∘ ρ = y)
    (P : G.IndexedPresentation BP)
    (U : SpecialTransformations.Section5.DefSet (M := M) R 1 a) (hBR : B.real ⊆ R)
    (hU : GammaSetDefinable B (carrier U)) (hSource : carrier U = vfSchemaSource A F)
    (hfin : ∀ (x : Fin 1 → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program) :
    GammaIsp hκ hs h00 hreal (gammaPrependSelectedContraction hκ hs hreal hBR hU ρ hfin T hT)
      (gammaSwapVolumeBlocks P.toGamma) := by
  apply gamma_volume_slice_unary_lift_uniformity hκ hs h00 hreal hgamma δ hδ hδ1 FBase
  intro t LP LQ
  let L := gammaLogicInput (⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ : Base (M := M))
  let f := gammaSelectedContractionSliceLiftIso hκ hs hreal hBR hU ρ hfin T hT t LP
  let g := gammaPreparedSelectedSliceLiftIso C e hA hC F G ρ hRows BP hG hLabels P t LQ
  have hSrc : carrier U ∩ {q | q.2 ∘ ρ = t} = vfSchemaSource A F ∩ {q | q.2 ∘ ρ = t} :=
    congrArg (fun E => E ∩ {q | q.2 ∘ ρ = t}) hSource
  exact ⟨(f.symm L).trans L (g.congr hSrc.symm rfl)⟩

end IntegrationInACVF.Section6
