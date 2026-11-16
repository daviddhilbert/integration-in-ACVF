module

public import Integration7.GenericRVPolydiscs
public import IntegrationSection6.GammaPreparedIndexPresentation

@[expose] public section

/-! A prepared cell with nonzero VF tags contains an inverse image
generic over the preparation's real base, and hence over any smaller
original real base. No preservation assertion is made on every fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

private theorem independent_over_subfield {K : Type} [Field K] {ι : Type} {x : ι → K}
    {E F : Subfield K} (h : E ≤ F) (hx : AlgebraicIndependent F x) :
    AlgebraicIndependent E x := by
  letI := (Subfield.inclusion h).toAlgebra
  letI : IsScalarTower E F K := .of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap E F) :=
    fun _ _ he => Subtype.ext (congrArg (fun z : F => z.val) he)
  exact hx.restrictScalars hinj

theorem independent_over_smaller_real_base {n : ℕ} {S R : Set M}
    (hSR : S ⊆ R) {x : Fin n → VFType (M := M)}
    (hx : AlgebraicIndependent (vfParameterField R) x) :
    AlgebraicIndependent (vfParameterField S) x := by
  exact independent_over_subfield (Subfield.closure_mono (fun _ hz => hSR hz)) hx

set_option maxHeartbeats 1600000 in
theorem exists_generic_inverse_in_prepared_cell {p l : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (M := M) (C.base : Set M) p 0}
    {Z : DefSet (M := M) (C.base : Set M) p l}
    (T : SpecialBijection A Z) (hZ : IsRVPullback (carrier Z))
    (x : Z) (hx : ∀ j, (rv (x.val.1 j)).val ≠ iRVZero) :
    ∃ y : Z, SameRV y.val x.val ∧
      AlgebraicIndependent (vfParameterField (C.base : Set M))
        (show Fin p → VFType (M := M) from (T.inverseMap y).val.1) := by
  obtain ⟨v,hv,hind⟩ := exists_independent_in_nonzero_rv_polydisc hc
    C.uncountable.le C.saturated (C.base : Set M) C.small
    (fun j => rv (x.val.1 j)) hx
  have hSame : SameRV (v,x.val.2) x.val := (sameRV_iff _ _).mpr
    ⟨fun j => congrFun hv j,rfl⟩
  let y : Z := ⟨(v,x.val.2),(mem_iff_sameRV hZ hSame).mpr x.property⟩
  have hInjective : Function.Injective T.inverseMap := by
    intro y z h
    have he := congrArg T.toMap h
    simpa only [SpecialBijection.apply_inverse] using he
  have hi := independent_map_of_finiteFibres hc (rawSpecialMap hc T.inverseMap)
    (SpecialTransformations.DefinableGeometry.Map.finiteFibres_of_injective hInjective) y hind
  exact ⟨y,hSame,hi⟩

end IntegrationInACVF.Section7
