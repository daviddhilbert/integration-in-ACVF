import IntegrationSection6.GammaSortedParameterElimination
import Section3.GammaDefinableClosureField
import Mathlib.SetTheory.Cardinal.Subfield

/-! Name the generated VF parameter field internally. Its names are
definable over the unchanged original Gamma base and can be eliminated.
The saturation bound applies to this generated field, not all RV codes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def vfFieldNames (B : Base (M := M)) : Set M :=
  Set.range (fun x : vfParameterField B.real => x.val.val)

def vfFieldNamedBase (B : Base (M := M)) : Base (M := M) := ⟨B.real ∪ vfFieldNames B,B.gamma⟩

def vfFieldNamedBase_field (B : Base (M := M)) : VFFieldBase (vfFieldNamedBase B).real where
  field := vfParameterField B.real
  mem_iff x := by
    constructor
    · intro hx
      exact Or.inr ⟨⟨x,hx⟩,rfl⟩
    · rintro (hx | ⟨y,hy⟩)
      · exact Subfield.subset_closure hx
      · have he : y.val = x := Subtype.ext hy
        exact he ▸ y.property

theorem vfFieldNames_definable (B : Base (M := M)) (c : M) (hc : c ∈ vfFieldNames B)
    (σ : SortTag) (hσ : sortEval σ c) : DefinableClosureAtBase B σ c := by
  obtain ⟨x,rfl⟩ := hc
  have he : σ = .vf := CanonicalStructure.sort_unique hM hσ x.val.property
  cases he
  exact vfParameterField_le_definableClosureFieldBase B x.property

theorem vfFieldNamedBase_eliminate {B : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {D : Set (Fin n → M)} (hD : DefinableOverBase (vfFieldNamedBase B) sn D) :
    DefinableOverBase B sn D := gamma_eliminate_added_real hD (vfFieldNames_definable B)

theorem vfFieldNamedBase_small (B : Base (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hB : Cardinal.mk B.real < κ) :
    Cardinal.mk (vfFieldNamedBase B).real < κ := by
  let T := {x : Transfer.VFType (M := M) | x.val ∈ B.real}
  have hT : Cardinal.mk T ≤ Cardinal.mk B.real :=
    Cardinal.mk_le_of_injective (f := fun x : T => (⟨x.val.val,x.property⟩ : B.real))
      (by intro x y h; exact Subtype.ext (Subtype.ext (congrArg (fun z : B.real => z.val) h)))
  have hF : Cardinal.mk (vfParameterField B.real) < κ :=
    (Subfield.cardinalMk_closure_le_max T).trans_lt (max_lt (hT.trans_lt hB) hκ)
  have hNames : Cardinal.mk (vfFieldNames B) < κ := Cardinal.mk_range_le.trans_lt hF
  exact (Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ.le hB hNames)

end IntegrationInACVF.Section6
