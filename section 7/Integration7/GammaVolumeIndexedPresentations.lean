import Integration7.GammaVolumeGraphPresentations
import Integration7.GammaVolumeSchemaDensityGraphs
import IntegrationSection6.GammaSchemaIndexedPresentations

/-! A volume schema over an RV index family has a full joint volume
presentation. The base's finite volume is appended to the fibre volume;
the density remains the original fibre density. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV Point GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def GammaRVVolumeSchema.indexedDensity
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv)) (T : Set (Fin p → RV (M := M)))
    (w : Fin (p+a) → RV (M := M)) (ω : Fin 1 → RV (M := M)) : Prop :=
  w ∈ indexedDomain T (fun t => F.object.rowDomain (rvValues t)) ∧
    F.rowDensity (rvValues (indexedLeft w)) (indexedRight w) ω

abbrev GammaRVVolumeSchema.IndexedPresentation
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv)) (BP : GammaFiniteGraphPresentation B p d T R) :=
  GammaVolumeGraphPresentation B (p+a) (d+(k+1))
    (indexedDomain T (fun t => F.object.rowDomain (rvValues t)))
    (fun w y => w ∈ indexedDomain T (fun t => F.object.rowDomain (rvValues t)) ∧
      indexedVolume BP.totalVolume (fun t => F.object.rowValue (rvValues t)) w = y)
    (F.indexedDensity T)

theorem GammaRVVolumeSchema.indexedDensity_graph
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) :
    GammaGraphDefinable B (fun (x : Point (M := M) 0 (p+a)) (y : Point (M := M) 0 1) =>
      F.indexedDensity T x.2 y.2) := by
  have hSort : Fin.append (Fin.append (fun _ : Fin p => SortTag.rv) (fun _ : Fin a => .rv))
      (fun _ : Fin 1 => .rv) = fun _ => .rv := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp only [Fin.append_left,Fin.append_right]
    · simp only [Fin.append_right]
  have hρ := F.density_definable
  rw [hSort] at hρ
  have hGraph := gamma_rv_graph_from_tuple_formula hρ
  have h := (gammaLogicInput B).restrict_graph (F.object.indexed_domain_graph BP) hGraph
  apply GammaGraphDefinable.congr h
  intro x y
  apply and_congr Iff.rfl
  have he : Fin.append (rvValues (indexedLeft x.2)) (rvValues (indexedRight x.2)) = rvValues x.2 := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [rvValues,indexedLeft,indexedRight,Function.comp_apply,Fin.append_left,Fin.append_right]
  change (Fin.append (rvValues x.2) (rvValues y.2) ∈ F.density) ↔
    (Fin.append (Fin.append (rvValues (indexedLeft x.2)) (rvValues (indexedRight x.2))) (rvValues y.2) ∈ F.density)
  rw [he]

theorem GammaRVVolumeSchema.exists_indexedVolumePresentation
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, F.valid (rvValues t)) : Nonempty (F.IndexedPresentation BP) := by
  let P := F.object.indexedPresentation BP (fun t ht => (hvalid t ht).1)
  apply exists_gammaVolumeGraphPresentation P (F.indexedDensity_graph BP)
  · intro w
    obtain ⟨ω,hω,hu⟩ := F.rowDensity_unique _ (hvalid _ w.property.1) ⟨_,w.property.2⟩
    exact ⟨ω,⟨w.property,hω⟩,fun y hy => hu y hy.2⟩
  · intro w ω h
    exact h.1
  · intro w ω h
    exact F.rowDensity_nonzero _ _ _ h.2

def GammaRVVolumeSchema.indexedVolumePresentation
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, F.valid (rvValues t)) : F.IndexedPresentation BP :=
  Classical.choice (F.exists_indexedVolumePresentation BP hvalid)

end IntegrationInACVF.Section7
