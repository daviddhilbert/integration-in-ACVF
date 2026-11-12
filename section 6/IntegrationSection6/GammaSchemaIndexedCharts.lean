import IntegrationSection6.GammaSchemaChartRows
import IntegrationSection6.GammaSchemaIndexedObjects

/-! Weighted chart schemata glue over a finite-volume RV base. The joint
chart preserves the actual index tuple; its complete graph is over the
original base and its volume weight appends the same base contribution. -/
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
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaFiniteRVIsoSchema.pureRV_chart_graph
    (H : GammaFiniteRVIsoSchema B p a b k (fun _ => .rv)) :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+a)) (y : Point (M := M) 0 b) =>
      Fin.append (fun j => (w.2 j).val) (fun j => (y.2 j).val) ∈ H.chart) := by
  have hs : Fin.append (Fin.append (fun _ : Fin p => SortTag.rv) (fun _ : Fin a => .rv))
      (fun _ : Fin b => .rv) = (fun _ => .rv) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp only [Fin.append_left,Fin.append_right]
    · simp only [Fin.append_right]
  exact gamma_rv_graph_from_tuple_formula (hs ▸ H.chart_definable)

theorem GammaFiniteRVIsoSchema.indexed_chart_graph
    (H : GammaFiniteRVIsoSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, H.valid (fun j => (t j).val)) :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+a)) (y : Point (M := M) 0 (p+b)) =>
      ∃ u : indexedDomain T (fun t => H.source.rowDomain (fun j => (t j).val)), u.val = w.2 ∧
        (indexedEquiv T (fun t => H.source.rowDomain (fun j => (t j).val))
          (fun t => H.target.rowDomain (fun j => (t j).val))
          (fun t => H.rowEquiv (fun j => (t.val j).val) (hvalid t.val t.property)) u).val = y.2) := by
  let par := rvCoordinatePointMap (Fin.castAdd a : Fin p → Fin (p+a)) B.real
  let par' := rvCoordinatePointMap (Fin.castAdd b : Fin p → Fin (p+b)) B.real
  let labels := rvCoordinatePointMap (Fin.natAdd p : Fin b → Fin (p+b)) B.real
  let ident := @Map.id M sM _ B.real (PresentedSet.univ (pointSpace (M := M) 0 (p+a)) B.real)
  have hEq := (gamma_global_map_graph par).preimage_maps ident par'
  have hChart := H.pureRV_chart_graph.preimage_maps ident labels
  have h := (gammaLogicInput B).restrict_graph (H.source.indexed_domain_graph BP) (hEq.inter hChart)
  apply GammaGraphDefinable.congr h
  intro w y
  have hSplit : (fun j => (w.2 j).val) = Fin.append (fun j => (w.2 (Fin.castAdd a j)).val)
      (fun j => (w.2 (Fin.natAdd p j)).val) :=
    (Fin.append_castAdd_natAdd (f := fun j => (w.2 j).val)).symm
  change (w.2 ∈ indexedDomain T (fun t => H.source.rowDomain (fun j => (t j).val)) ∧
    ((Fin.elim0,w.2 ∘ Fin.castAdd a) = (Fin.elim0,y.2 ∘ Fin.castAdd b) ∧
      Fin.append (fun j => (w.2 j).val) (fun j => (y.2 (Fin.natAdd p j)).val) ∈ H.chart)) ↔ _
  rw [hSplit]
  let D := fun t : Fin p → RV (M := M) => H.source.rowDomain (fun j => (t j).val)
  let E := fun t : Fin p → RV (M := M) => H.target.rowDomain (fun j => (t j).val)
  let e := fun t : T => H.rowEquiv (fun j => (t.val j).val) (hvalid t.val t.property)
  constructor
  · rintro ⟨hw,heq,hc⟩
    have hPar : indexedLeft w.2 = indexedLeft y.2 := congrArg Prod.snd heq
    have hy : indexedRight y.2 ∈ E (indexedLeft w.2) :=
      ((hvalid _ hw.1).2.2.1.2 (fun j => (y.2 (Fin.natAdd p j)).val)).mpr
        ⟨fun j => (w.2 (Fin.natAdd p j)).val,hc⟩
    let u : indexedDomain T D := ⟨w.2,hw⟩
    have hxy : (e ⟨indexedLeft w.2,hw.1⟩ ⟨indexedRight w.2,hw.2⟩).val = indexedRight y.2 :=
      congrArg Subtype.val ((H.rowEquiv_graph _ (hvalid _ hw.1) ⟨indexedRight w.2,hw.2⟩ ⟨_,hy⟩).mp hc)
    refine ⟨u,rfl,?_⟩
    rw [indexedEquiv_labels,hxy,hPar]
    exact Fin.append_castAdd_natAdd
  · rintro ⟨u,hu,huy⟩
    rw [← hu,← huy]
    refine ⟨u.property,?_,?_⟩
    · exact Prod.ext (Subsingleton.elim _ _) (indexedEquiv_left T D E e u).symm
    · change Fin.append (Fin.append (fun j => (indexedLeft u.val j).val)
        (fun j => (indexedRight u.val j).val))
        (fun j => (indexedRight (indexedEquiv T D E e u).val j).val) ∈ H.chart
      rw [indexedEquiv_right]
      exact H.rowEquiv_apply _ (hvalid _ u.property.1) ⟨indexedRight u.val,u.property.2⟩

def GammaFiniteRVIsoSchema.indexedIso
    (H : GammaFiniteRVIsoSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, H.valid (fun j => (t j).val))
    (P : GammaFiniteGraphPresentation B (p+a) (d+k)
      (indexedDomain T (fun t => H.source.rowDomain (fun j => (t j).val)))
      (fun w y => w ∈ indexedDomain T (fun t => H.source.rowDomain (fun j => (t j).val)) ∧
        indexedVolume BP.totalVolume (fun t => H.source.rowValue (fun j => (t j).val)) w = y))
    (Q : GammaFiniteGraphPresentation B (p+b) (d+k)
      (indexedDomain T (fun t => H.target.rowDomain (fun j => (t j).val)))
      (fun w y => w ∈ indexedDomain T (fun t => H.target.rowDomain (fun j => (t j).val)) ∧
        indexedVolume BP.totalVolume (fun t => H.target.rowValue (fun j => (t j).val)) w = y)) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  refine gammaIndexedIso T _ _ BP.totalVolume _ _ P Q
    (fun t => H.rowEquiv (fun j => (t.val j).val) (hvalid t.val t.property))
    (H.indexed_chart_graph BP hvalid) ?_
  intro t x
  apply H.valid_weight (hvalid t.val t.property) x.val (H.rowEquiv _ (hvalid t.val t.property) x).val
  · exact H.rowEquiv_apply _ (hvalid t.val t.property) x
  · exact (H.source.rowValue_graph _ (hvalid t.val t.property).1 x.val x.property _).mpr rfl
  · exact (H.target.rowValue_graph _ (hvalid t.val t.property).2.1 _
      (H.rowEquiv _ (hvalid t.val t.property) x).property _).mpr rfl

end IntegrationInACVF.Section6
