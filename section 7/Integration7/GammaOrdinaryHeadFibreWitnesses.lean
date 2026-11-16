module

public import Integration7.GenericCoordinateFibreDimension
public import IntegrationSection6.VFParameterFibreIsomorphisms
public import IntegrationSection6.GammaHeadFibreParameters

@[expose] public section

/-! Ordinary point-row isomorphisms at generic full VF tuples remain
actual original-Gamma isomorphisms after freezing a generic VF tail. -/
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

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p n a b : ℕ}

theorem vf_parameter_empty_fibre_domain
    (U : DefSet (M := M) S p a) (y : Fin p → VF (M := M)) :
    vfParameterFibre (p := p) (n := 0) (carrier U) y =
      {q : Point (M := M) 0 a | (y,q.2) ∈ carrier U} := by
  ext q
  change (Fin.append y q.1,q.2) ∈ carrier U ↔ (y,q.2) ∈ carrier U
  have h : Fin.append y q.1 = y := funext (fun i => Fin.append_left y q.1 i)
  rw [h]

theorem head_point_fibre_domain
    (U : DefSet (M := M) S (n+1) a) (x : Fin n → VF (M := M)) (z : Fin 1 → VF (M := M)) :
    {q : Point (M := M) 0 a | (Fin.cons (z 0) x,q.2) ∈ carrier U} =
      {q : Point (M := M) 0 a | (z,q.2) ∈ carrier (coordinateFibre U 0 (headFrozenTuple x))} := by
  ext q
  change (Fin.cons (z 0) x,q.2) ∈ carrier U ↔
    coordinateInsert 0 (headFrozenTuple x) (z,q.2) ∈ carrier U
  rw [coordinateInsert_head]
  rfl

theorem generic_head_ordinary_row_iso
    (U : DefSet (M := M) S (n+1) a) (V : DefSet (M := M) S (n+1) b)
    (hCommon : ∀ y : Fin (n+1) → VF (M := M), AlgebraicIndependent (vfParameterField B.real) y →
      Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (y j).val),B.gamma⟩
        {q : Point (M := M) 0 a | (y,q.2) ∈ carrier U}
        {q : Point (M := M) 0 b | (y,q.2) ∈ carrier V}))
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (z : Fin 1 → VF (M := M))
    (hz : AlgebraicIndependent (vfParameterField (B.real ∪ Set.range (fun j => (x j).val))) z) :
    Nonempty (GammaIso ⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪ Set.range (vfValues z),B.gamma⟩
      {q : Point (M := M) 0 a | (z,q.2) ∈ carrier (coordinateFibre U 0 (headFrozenTuple x))}
      {q : Point (M := M) 0 b | (z,q.2) ∈ carrier (coordinateFibre V 0 (headFrozenTuple x))}) := by
  have hField := vfParameterField_union_tuple B.real x
  have hz' : AlgebraicIndependent (tupleField (vfParameterField B.real) x) z :=
    Eq.mp (congrArg (fun E : Subfield (VFType (M := M)) => AlgebraicIndependent E z) hField) hz
  obtain ⟨e⟩ := hCommon (Fin.cons (z 0) x)
    (independent_cons_over_tuple_field (vfParameterField B.real) x z hx hz')
  have hBase := headVFParameterBase (B := B) x z
  exact Eq.mp (congrArg (fun L : Base (M := M) => Nonempty (GammaIso L
    {q : Point (M := M) 0 a | (z,q.2) ∈ carrier (coordinateFibre U 0 (headFrozenTuple x))}
    {q : Point (M := M) 0 b | (z,q.2) ∈ carrier (coordinateFibre V 0 (headFrozenTuple x))})) hBase.symm)
    ⟨e.congr (head_point_fibre_domain U x z) (head_point_fibre_domain V x z)⟩

end IntegrationInACVF.Section7
