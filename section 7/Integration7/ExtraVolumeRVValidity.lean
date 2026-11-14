import Integration7.ExtraVolumeParameters

/-! First-order RV validity with auxiliary parameters confined to the
exception map. The objects, density graphs, chart and chart supports are
all formulas over the original parameter block. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k j : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def extraWeightedPairsOutsideException (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (H : Set (Fin ((p+a)+b) → M))
    (E : GammaFiniteRVSchema B (p+q) ((k+1)+1) j (Fin.append sp sq)) :
    Set (Fin ((p+q)+(((k+1)+1)+((k+1)+1))) → M) :=
  {w | (w ∘ dropExtraVolumeParameters p q (((k+1)+1)+((k+1)+1)) ∈
      schemaVolumeCorrespondence (weightedVolumeSchema F) (weightedVolumeSchema G) H ∧
    w ∘ weightedPairSourceIndices (p+q) (k+1) ∉ E.domain) ∧
    w ∈ sortedUniverse (Fin.append (Fin.append sp sq) (fun _ : Fin (((k+1)+1)+((k+1)+1)) => .rv))}

theorem extraWeightedPairsOutsideException_definable
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (E : GammaFiniteRVSchema B (p+q) ((k+1)+1) j (Fin.append sp sq)) :
    DefinableOverBase B
      (Fin.append (Fin.append sp sq) (fun _ : Fin (((k+1)+1)+((k+1)+1)) => .rv))
      (extraWeightedPairsOutsideException F G H E) := by
  let st := Fin.append (Fin.append sp sq) (fun _ : Fin (((k+1)+1)+((k+1)+1)) => SortTag.rv)
  have hC := (schemaVolumeCorrespondence_definable (weightedVolumeSchema F) (weightedVolumeSchema G) hH).preimage_real
    st (dropExtraVolumeParameters p q (((k+1)+1)+((k+1)+1)))
  have hE := E.domain_definable.preimage_real st (weightedPairSourceIndices (p+q) (k+1))
  have h := hC.inter hE.compl
  convert h using 1
  ext w
  change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ ¬(_ ∧ _)))
  tauto

def extraVolumeJacobianFormula (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (H : Set (Fin ((p+a)+b) → M))
    (A : Finset (SpecialTransformations.Section9.VolumeChartSupport (k+1))) :
    Set (Fin ((p+q)+(((k+1)+1)+((k+1)+1))) → M) :=
  {w | w ∘ dropExtraVolumeParameters p q (((k+1)+1)+((k+1)+1)) ∈ supportedSchemaJacobianFormula F G H A ∧
    w ∈ sortedUniverse (Fin.append (Fin.append sp sq) (fun _ : Fin (((k+1)+1)+((k+1)+1)) => .rv))}

theorem extraVolumeJacobianFormula_definable
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (A : Finset (SpecialTransformations.Section9.VolumeChartSupport (k+1))) :
    DefinableOverBase B
      (Fin.append (Fin.append sp sq) (fun _ : Fin (((k+1)+1)+((k+1)+1)) => .rv))
      (extraVolumeJacobianFormula (q := q) (sq := sq) F G H A) :=
  (supportedSchemaJacobianFormula_definable hc F G hH A).preimage_real _
    (dropExtraVolumeParameters p q (((k+1)+1)+((k+1)+1)))

def extraVolumeChartRVRowValid (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (H : Set (Fin ((p+a)+b) → M))
    (A : Finset (SpecialTransformations.Section9.VolumeChartSupport (k+1)))
    (E : GammaFiniteRVSchema B (p+q) ((k+1)+1) j (Fin.append sp sq)) (w : Fin (p+q) → M) : Prop :=
  (∀ i, sortEval (Fin.append sp sq i) (w i)) ∧
    ∀ r, Fin.append w r ∈ extraWeightedPairsOutsideException F G H E →
      Fin.append w r ∈ extraVolumeJacobianFormula (q := q) (sq := sq) F G H A

theorem extraVolumeChartRVRowValid_definable
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (A : Finset (SpecialTransformations.Section9.VolumeChartSupport (k+1)))
    (E : GammaFiniteRVSchema B (p+q) ((k+1)+1) j (Fin.append sp sq)) :
    DefinableOverBase B (Fin.append sp sq) {w | extraVolumeChartRVRowValid F G H A E w} :=
  gamma_family_row_subset_definable (Fin.append sp sq) _
    (extraWeightedPairsOutsideException_definable F G hH E)
    (extraVolumeJacobianFormula_definable hc F G hH A)

end IntegrationInACVF.Section7
