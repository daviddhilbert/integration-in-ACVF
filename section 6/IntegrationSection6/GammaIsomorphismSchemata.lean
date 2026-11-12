import IntegrationSection6.GammaFiniteObjectSchemata
import IntegrationSection6.GammaFamilyBijectionValidity
import IntegrationSection6.GammaWeightValidity
import IntegrationSection6.GammaTupleRelationSpecialization

/-! Finite RV-isomorphism schemata carry actual source/target object
schemata, a full chart formula, and first-order bijectivity/weight validity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure GammaFiniteRVIsoSchema (B : Base (M := M)) (p a b k : ℕ) (sp : Fin p → SortTag := fun _ => .vf) where
  source : GammaFiniteRVSchema B p a k sp
  target : GammaFiniteRVSchema B p b k sp
  chart : Set (Fin ((p+a)+b) → M)
  chart_definable : DefinableOverBase B
    (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) chart

variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteRVIsoSchema.valid (F : GammaFiniteRVIsoSchema B p a b k sp) (z : Fin p → M) : Prop :=
  F.source.valid z ∧ F.target.valid z ∧
  bijectiveMapRowValid sp (fun _ => .rv) F.source.domain F.target.domain F.chart z ∧
  weightedChartRowValid sp F.chart F.source.volume F.target.volume z

theorem GammaFiniteRVIsoSchema.valid_definable (F : GammaFiniteRVIsoSchema B p a b k sp) :
    DefinableOverBase B sp {z | F.valid z} :=
  F.source.valid_definable.inter (F.target.valid_definable.inter
    ((gamma_bijection_validity_definable _ _ _ F.source.domain_definable F.target.domain_definable F.chart_definable).inter
      (gamma_weighted_chart_validity_definable _ F.chart_definable F.source.volume_definable F.target.volume_definable)))

theorem GammaFiniteRVIsoSchema.valid_weight (F : GammaFiniteRVIsoSchema B p a b k sp)
    {z : Fin p → M} (hz : F.valid z)
    (x : Fin a → RV (M := M)) (y : Fin b → RV (M := M))
    (u v : Fin k → RV (M := M))
    (hH : Fin.append (Fin.append z (fun j => (x j).val)) (fun j => (y j).val) ∈ F.chart)
    (hF : F.source.rowVolume z x u) (hG : F.target.rowVolume z y v) :
    rawWeight (fun j => (u j).val) = rawWeight (fun j => (v j).val) := by
  let r : Fin ((a+b)+(k+k)) → M :=
    Fin.append (Fin.append (fun j => (x j).val) (fun j => (y j).val))
      (Fin.append (fun j => (u j).val) (fun j => (v j).val))
  have hx : chartRowX a b k r = fun j => (x j).val := by
    funext j
    simp only [chartRowX,r,Fin.append_left]
  have hy : chartRowY a b k r = fun j => (y j).val := by
    funext j
    simp only [chartRowY,r,Fin.append_left,Fin.append_right]
  have hu : chartRowU a b k r = fun j => (u j).val := by
    funext j
    simp only [chartRowU,r,Fin.append_left,Fin.append_right]
  have hv : chartRowV a b k r = fun j => (v j).val := by
    funext j
    simp only [chartRowV,r,Fin.append_right]
  have hr : ∀ j, iRV (r j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [r,Fin.append_left] using (x l).property
      · simpa only [r,Fin.append_left,Fin.append_right] using (y l).property
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [r,Fin.append_right,Fin.append_left] using (u l).property
      · simpa only [r,Fin.append_right] using (v l).property
  have hw := hz.2.2.2.2 r hr
  rw [hx,hy,hu,hv] at hw
  exact hw hH hF hG

end IntegrationInACVF.Section6
