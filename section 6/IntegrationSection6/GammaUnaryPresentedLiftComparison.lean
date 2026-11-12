import IntegrationSection6.GammaUnarySliceUniformityWithoutField
import IntegrationSection6.GammaPreparedSelectedSliceIsomorphisms

/-! The unary preparation comparison only needs the actual selected-slice
lift representation. This form applies to a head preparation inside a
longer coordinate contraction. -/
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
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {l a k : ℕ}
open FiniteRV

theorem gamma_unary_prepared_lift_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {A : Set (Point (M := M) 1 0)}
    (C : DefSet (M := M) S 1 l) (e : GammaIso B A (carrier C))
    (hA : GammaSetDefinable B A) (hC : IsRVPullback (carrier C))
    (F : GammaFiniteRVSchema B 1 a k) (G : GammaFiniteRVSchema B (1+l) a k (fun _ => .rv))
    (ρ : Fin k → Fin a)
    (hRows : ∀ c : C, GammaSchemaRowAgreement F (rawVFParameter (e.equiv.symm c).val) G (rawPreparedKey c.val))
    (BP : PreparedIndexPresentation B C)
    (hG : ∀ s ∈ preparedKeyDomain C, G.finiteRow (fun j => (s j).val))
    (hLabels : ∀ s ∈ preparedKeyDomain C, ∀ r y, G.rowVolume (fun j => (s j).val) r y ↔
      r ∈ G.rowDomain (fun j => (s j).val) ∧ r ∘ ρ = y)
    (P : G.IndexedPresentation BP) (Z : GammaRVFiniteObject B (k+1))
    (hLift : ∀ t : Fin k → RV (M := M),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (rvObjectArity Z.object) 1 ((gammaVolumeSliceSchema Z).rowDomain (fun j => (t j).val))
        ((gammaVolumeSliceSchema Z).rowVolume (fun j => (t j).val)),
      Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
        (vfSchemaSource A F ∩ {q | q.2 ∘ ρ = t}) Q.toGamma.lift)) :
    GammaIsp hκ.le hs h00 hreal Z (gammaSwapVolumeBlocks P.toGamma) := by
  apply gamma_volume_slice_unary_lift_uniformity_uncountable hκ hs h00 hreal hgamma δ hδ hδ1
  intro t LP LQ
  obtain ⟨f⟩ := hLift t LP
  let g := gammaPreparedSelectedSliceLiftIso C e hA hC F G ρ hRows BP hG hLabels P t LQ
  exact ⟨(f.symm (gammaLogicInput _)).trans (gammaLogicInput _) g⟩

end IntegrationInACVF.Section6
