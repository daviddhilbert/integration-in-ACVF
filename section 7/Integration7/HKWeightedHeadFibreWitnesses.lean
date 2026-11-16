import Integration7.GammaOrdinaryHeadFibreWitnesses
import Integration7.HKWeightedPointIsomorphismCongruence
import IntegrationSection6.VFParameterFibreIsomorphisms
import IntegrationSection6.GammaHeadFibreParameters

/-! Freezing a generic VF tail retains exact density equations in
the resulting original-Gamma unary row isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p n a b : ℕ}

theorem generic_head_weighted_row_iso
    (U : DefSet (M := M) S (n+1) a) (V : DefSet (M := M) S (n+1) b)
    (δ : Fin a) (ε : Fin b)
    (hCommon : ∀ y : Fin (n+1) → VF (M := M), AlgebraicIndependent (vfParameterField B.real) y →
      ∃ e : GammaIso ⟨B.real ∪ Set.range (fun j => (y j).val),B.gamma⟩
        {q : Point (M := M) 0 a | (y,q.2) ∈ carrier U}
        {q : Point (M := M) 0 b | (y,q.2) ∈ carrier V},
        ∀ u, u.val.2 δ = (e.equiv u).val.2 ε)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (z : Fin 1 → VF (M := M))
    (hz : AlgebraicIndependent (vfParameterField (B.real ∪ Set.range (fun j => (x j).val))) z) :
    ∃ e : GammaIso ⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪ Set.range (vfValues z),B.gamma⟩
      {q : Point (M := M) 0 a | (z,q.2) ∈ carrier (coordinateFibre U 0 (headFrozenTuple x))}
      {q : Point (M := M) 0 b | (z,q.2) ∈ carrier (coordinateFibre V 0 (headFrozenTuple x))},
      ∀ u, u.val.2 δ = (e.equiv u).val.2 ε := by
  have hField := vfParameterField_union_tuple B.real x
  have hz' : AlgebraicIndependent (tupleField (vfParameterField B.real) x) z :=
    Eq.mp (congrArg (fun E : Subfield (VFType (M := M)) => AlgebraicIndependent E z) hField) hz
  obtain ⟨e,he⟩ := hCommon (Fin.cons (z 0) x)
    (independent_cons_over_tuple_field (vfParameterField B.real) x z hx hz')
  have hBase := headVFParameterBase (B := B) x z
  exact Eq.mp (congrArg (fun L : Base (M := M) => ∃ f : GammaIso L
    {q : Point (M := M) 0 a | (z,q.2) ∈ carrier (coordinateFibre U 0 (headFrozenTuple x))}
    {q : Point (M := M) 0 b | (z,q.2) ∈ carrier (coordinateFibre V 0 (headFrozenTuple x))},
      ∀ u, u.val.2 δ = (f.equiv u).val.2 ε) hBase.symm)
    ⟨e.congr (head_point_fibre_domain U x z) (head_point_fibre_domain V x z),
      weighted_point_iso_congr_density e (head_point_fibre_domain U x z)
        (head_point_fibre_domain V x z) δ ε he⟩

end IntegrationInACVF.Section7.HK
