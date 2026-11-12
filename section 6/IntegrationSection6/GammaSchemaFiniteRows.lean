import IntegrationSection6.GammaSchemaRowValues
import IntegrationSection6.GammaSchemaRowEquality

/-! Bound-independent finite row semantics. Derived geometric families
need not share a chosen cardinality bound; their actual functionality and
finite volume fibres suffice for indexed assembly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteRVSchema.finiteRow (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) : Prop :=
  (∀ x ∈ F.rowDomain z, ∃! y : Fin k → RV (M := M), F.rowVolume z x y) ∧
  (∀ x y, F.rowVolume z x y → x ∈ F.rowDomain z) ∧
  (∀ y : Fin k → RV (M := M), {x : Fin a → RV (M := M) | F.rowVolume z x y}.Finite)

theorem GammaFiniteRVSchema.finiteRow_of_valid (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) : F.finiteRow z :=
  ⟨F.row_volume_unique z hz,fun x y hxy => hz.2.2.1 _ _ hxy,F.row_volume_finite z hz⟩

theorem GammaFiniteRVSchema.rowValue_graph_of_finiteRow (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : F.finiteRow z) (x : Fin a → RV (M := M)) (hx : x ∈ F.rowDomain z)
    (y : Fin k → RV (M := M)) : F.rowVolume z x y ↔ F.rowValue z x = y := by
  have hspec : F.rowVolume z x (F.rowValue z x) := by
    unfold GammaFiniteRVSchema.rowValue
    rw [dif_pos (hz.1 x hx)]
    exact (hz.1 x hx).exists.choose_spec
  constructor
  · intro hy
    exact (hz.1 x hx).unique hspec hy
  · exact fun hy => hy ▸ hspec

theorem GammaFiniteRVSchema.rowValue_finite_of_finiteRow (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : F.finiteRow z) (y : Fin k → RV (M := M)) :
    {x : Fin a → RV (M := M) | x ∈ F.rowDomain z ∧ F.rowValue z x = y}.Finite :=
  (hz.2.2 y).subset (fun x hx => (F.rowValue_graph_of_finiteRow z hz x hx.1 y).mpr hx.2)

theorem GammaFiniteRVSchema.finiteRow_congr (F G : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (h : F.sameRow G z) : F.finiteRow z ↔ G.finiteRow z := by
  have hD := F.sameRow_domains G h
  have hV := F.sameRow_volumes G h
  unfold GammaFiniteRVSchema.finiteRow
  rw [hD,hV]

end IntegrationInACVF.Section6
