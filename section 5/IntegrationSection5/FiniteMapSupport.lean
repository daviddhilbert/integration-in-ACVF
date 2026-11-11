import Section5.Core

/-! A finite internal real base supports an actual definable set and full
map graph simultaneously. This is a consequence of finite formulas and
adds no smallness assumption to the given working presentation. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace IntegrationInACVF.Section5
open SpecialTransformations.DefinableGeometry
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}

theorem finite_map_support (f : Map A B) :
    ∃ R : Set M, R.Finite ∧ R ⊆ S ∧ P.Definable R A.carrier ∧
      P.RelationDefinable Q R (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y) := by
  obtain ⟨U,hUS,hU⟩ := Set.definable_iff_finitely_definable.mp A.definable
  obtain ⟨V,hVS,hV⟩ := Set.definable_iff_finitely_definable.mp f.graph_definable
  let R : Set M := (U : Set M) ∪ V
  refine ⟨R,U.finite_toSet.union V.finite_toSet,Set.union_subset hUS hVS,?_,?_⟩
  · exact hU.mono Set.subset_union_left
  · exact hV.mono Set.subset_union_right

end IntegrationInACVF.Section5
