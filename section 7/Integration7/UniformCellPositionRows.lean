module

public import Integration7.UniformMixedCellPresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual position row on each parameter fibre, tied to the one
global positioning map. This supplies compatible positions for the
balanced and rectangle family cases without naming new VF choices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}
variable {G : Base (M := M)} {A : Set (Point (M := M) 2 m)}

namespace UniformMixedCellPresentation

def row (F : UniformMixedCellPresentation G A) (a : A) :
    PositionRow F.labels (F.vertical.scalarProjection a) (GammaScalarFamilies.value F.vertical.position)
      F.vertical.paradigm_index := Classical.choice (F.rows (F.vertical.scalarProjection a))

def localPosition (F : UniformMixedCellPresentation G A) (a : A) : VF (M := M) → VF (M := M) := (F.row a).position

theorem parameter_fibre_relation (F : UniformMixedCellPresentation G A) (a : A) :
    mixedPairFibre F.parameters a = CellsFromFibres.relation (F.row a).domain (F.localPosition a)
      ((F.vertical.projection a).val.2 F.vertical.paradigm_index) := F.vertical.pullback_fibre F.labels a (F.row a)

theorem local_position_cell_data (F : UniformMixedCellPresentation G A) (a : A) :
    Cells.CellData (mixedPairFibre F.parameters a) (F.localPosition a)
      ((F.vertical.projection a).val.2 F.vertical.paradigm_index) := by
  have hPoly := mixed_pair_fibre_polydisc F.parameters (fun a b he => F.parameters_reflect_same_rv a b he) a
  have hEq := F.parameter_fibre_relation a
  rw [hEq] at hPoly
  have hCell := (F.row a).cell hPoly
  rw [hEq]
  exact hCell

theorem centre_eq_local_position (F : UniformMixedCellPresentation G A) (a b : A)
    (he : F.parameters.toFun b = F.parameters.toFun a) : F.centre b = F.localPosition a (vfAt b.val 1) := by
  let u := F.vertical.scalarProjection b
  let u₀ := F.vertical.scalarProjection a
  let f := GammaScalarFamilies.value F.vertical.position
  have hu := (Set.ext_iff.mp (F.row a).fibre u.val).mp ⟨u,rfl,he⟩
  have hx : vfAt u.val 0 = vfAt b.val 1 := F.vertical.first b
  have hxD : vfAt b.val 1 ∈ (F.row a).domain := hx ▸ hu.1
  have hContext : GammaFamilySyntax.labels u.val = GammaFamilySyntax.labels u₀.val :=
    congrArg (fun r : Fin F.vertical.arity → RV (M := M) => fun i => (r i).val) hu.2
  have hValue := (F.row a).value (vfAt b.val 1) hxD
  rw [← hContext] at hValue
  have hArg : f (GammaFamilySyntax.labels u.val) (vfAt u.val 0).val =
      f (GammaFamilySyntax.labels u.val) (vfAt b.val 1).val := congrArg (fun x : VF (M := M) => f (GammaFamilySyntax.labels u.val) x.val) hx
  apply Subtype.ext
  exact (GammaScalarFamilies.value_on F.vertical.position (F.vertical.projection b)).symm.trans
    (hArg.trans hValue.symm)

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
