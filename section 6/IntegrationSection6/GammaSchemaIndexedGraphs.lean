import IntegrationSection6.GammaPureRVSchemaGraphs
import IntegrationSection6.GammaSchemaFiniteRows
import IntegrationSection6.GammaPresentationTotalVolume
import IntegrationSection6.GammaFamilyCoordinates

/-! Actual joint domain and volume graphs for a finite RV schema over an
RV[k] index object. The index volume is appended to the fibre volume. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaFiniteRVSchema.indexed_domain_graph
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (P : GammaFiniteGraphPresentation B p d T R) :
    GammaSetDefinable B {w : Point (M := M) 0 (p+a) |
      w.2 ∈ indexedDomain T (fun t => F.rowDomain (fun j => (t j).val))} := by
  let par := rvCoordinatePointMap (Fin.castAdd a : Fin p → Fin (p+a)) B.real
  have h := (gammaLogicInput B).inter (gamma_global_preimage par P.domain_graph) F.pureRV_domain_graph
  convert h using 1
  apply Set.ext
  intro w
  change (_ ∧ _) ↔ (_ ∧ _)
  have he : Fin.append (fun j => (w.2 (Fin.castAdd a j)).val)
      (fun j => (w.2 (Fin.natAdd p j)).val) = (fun j => (w.2 j).val) := Fin.append_castAdd_natAdd (f := fun j => (w.2 j).val)
  exact and_congr Iff.rfl (Iff.of_eq (congrArg (fun v => v ∈ F.domain) he))

theorem GammaFiniteRVSchema.indexed_volume_graph
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (P : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, F.finiteRow (fun j => (t j).val)) :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+a)) (y : Point (M := M) 0 (d+k)) =>
      w.2 ∈ indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) ∧
      indexedVolume P.totalVolume (fun t => F.rowValue (fun j => (t j).val)) w.2 = y.2) := by
  let par := rvCoordinatePointMap (Fin.castAdd a : Fin p → Fin (p+a)) B.real
  let base := rvCoordinatePointMap (Fin.castAdd k : Fin d → Fin (d+k)) B.real
  let fibre := rvCoordinatePointMap (Fin.natAdd d : Fin k → Fin (d+k)) B.real
  let ident := @Map.id M sM _ B.real (PresentedSet.univ (pointSpace (M := M) 0 (p+a)) B.real)
  have hBase := P.totalVolume_definable.preimage_maps par base
  have hFibre := F.pureRV_volume_graph.preimage_maps ident fibre
  have h := (gammaLogicInput B).restrict_graph (F.indexed_domain_graph P) (hBase.inter hFibre)
  apply GammaGraphDefinable.congr h
  intro w y
  change (w.2 ∈ indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) ∧
    ((w.2 ∘ Fin.castAdd a ∈ T ∧ P.totalVolume (w.2 ∘ Fin.castAdd a) = y.2 ∘ Fin.castAdd k) ∧
      Fin.append (fun j => (w.2 j).val) (fun j => (y.2 (Fin.natAdd d j)).val) ∈ F.volume)) ↔ _
  have he : (fun j => (w.2 j).val) = Fin.append (fun j => (w.2 (Fin.castAdd a j)).val)
      (fun j => (w.2 (Fin.natAdd p j)).val) := (Fin.append_castAdd_natAdd (f := fun j => (w.2 j).val)).symm
  rw [he]
  constructor
  · rintro ⟨hw,⟨_,hb⟩,hf⟩
    have hv := (F.rowValue_graph_of_finiteRow _ (hvalid _ hw.1) _ hw.2 _).mp hf
    refine ⟨hw,?_⟩
    change Fin.append _ _ = y.2
    exact (congrArg₂ Fin.append hb hv).trans Fin.append_castAdd_natAdd
  · rintro ⟨hw,hv⟩
    have hb : P.totalVolume (indexedLeft w.2) = y.2 ∘ Fin.castAdd k := by
      funext j
      simpa only [indexedVolume,Fin.append_left,Function.comp_apply] using congrFun hv (Fin.castAdd k j)
    have hf : F.rowValue (fun j => (indexedLeft w.2 j).val) (indexedRight w.2) = y.2 ∘ Fin.natAdd d := by
      funext j
      simpa only [indexedVolume,Fin.append_right,Function.comp_apply] using congrFun hv (Fin.natAdd d j)
    exact ⟨hw,⟨hw.1,hb⟩,(F.rowValue_graph_of_finiteRow _ (hvalid _ hw.1) _ hw.2 _).mpr hf⟩

end IntegrationInACVF.Section6
