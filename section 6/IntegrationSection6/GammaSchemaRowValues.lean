import IntegrationSection6.GammaSortedSchemaRows

/-! Actual typed volume values and finite fibres in every valid row of a
finite RV schema. The total extension outside valid domain rows is used
only as notation; all geometric graphs remain explicitly restricted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem GammaFiniteRVSchema.row_volume_unique (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : Fin a → RV (M := M)) (hx : x ∈ F.rowDomain z) :
    ∃! y : Fin k → RV (M := M), F.rowVolume z x y := by
  obtain ⟨v,hv,hu⟩ := hz.2.1 (fun j => (x j).val) hx
  have hvSort (j : Fin k) : iRV (v j) := by
    simpa only [Fin.append_right,sortEval,iRV] using F.volume_definable.proper _ hv (Fin.natAdd (p+a) j)
  refine ⟨fun j => ⟨v j,hvSort j⟩,hv,?_⟩
  intro y hy
  funext j
  exact Subtype.ext (congrFun (hu (fun j => (y j).val) hy) j)

theorem GammaFiniteRVSchema.row_volume_finite (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (y : Fin k → RV (M := M)) :
    {x : Fin a → RV (M := M) | F.rowVolume z x y}.Finite := by
  have hy : ∀ j, sortEval SortTag.rv (y j).val := by
    intro j
    exact (y j).property
  have hf := (hz.2.2.2 (fun j => (y j).val) hy).1
  apply hf.of_injOn (f := fun x : Fin a → RV (M := M) => fun j => (x j).val)
  · intro x hx
    exact hx
  · intro x hx x' hx' he
    funext j
    exact Subtype.ext (congrFun he j)

def GammaFiniteRVSchema.rowValue (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (x : Fin a → RV (M := M)) : Fin k → RV (M := M) :=
  if h : ∃! y : Fin k → RV (M := M), F.rowVolume z x y then h.exists.choose else fun _ => 0

theorem GammaFiniteRVSchema.rowValue_graph (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : Fin a → RV (M := M)) (hx : x ∈ F.rowDomain z)
    (y : Fin k → RV (M := M)) : F.rowVolume z x y ↔ F.rowValue z x = y := by
  have hspec : F.rowVolume z x (F.rowValue z x) := by
    unfold GammaFiniteRVSchema.rowValue
    rw [dif_pos (F.row_volume_unique z hz x hx)]
    exact (F.row_volume_unique z hz x hx).exists.choose_spec
  have hu := F.row_volume_unique z hz x hx
  constructor
  · intro hy
    exact (hu.unique hspec hy)
  · exact fun hy => hy ▸ hspec

theorem GammaFiniteRVSchema.rowValue_finite_fibres (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (y : Fin k → RV (M := M)) :
    {x : Fin a → RV (M := M) | x ∈ F.rowDomain z ∧ F.rowValue z x = y}.Finite :=
  (F.row_volume_finite z hz y).subset (fun x hx => (F.rowValue_graph z hz x hx.1 y).mpr hx.2)

end IntegrationInACVF.Section6
