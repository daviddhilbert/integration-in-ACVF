import IntegrationSection6.VFPrefixUnaryFibreAgreement
import IntegrationSection6.SpecialEqualityTransport

/-! Restricting a relatively special head preparation to a frozen VF tail
retains actual unary special chains. Only internal presentations are
extended; no new special-bijection existence input is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n p a b : ℕ}
variable {U : DefSet (M := M) S (n+(p+1)) a} {V : DefSet (M := M) S (n+(p+1)) b}

theorem specialRelative_vfPrefix (f : Map U V) (hf : SpecialRelative f 0)
    (x : Fin n → VF (M := M)) :
    SpecialRelative (vfPrefixFibreMap f (vfPrefixRelative_of_unaryHead f hf.choose) x) 0 := by
  obtain ⟨hi,hT⟩ := hf
  refine ⟨vfPrefixFibreMap_unaryHead f hi x,?_⟩
  intro u
  obtain ⟨T,hT⟩ := hT (vfPrefixTuple x u)
  let hAug := vfPrefixHeadFibre_parameters (S := S) x u
  have hU : extendBase (coordinateFibre U 0 (vfPrefixTuple x u)) hAug = coordinateFibre (vfPrefixFibre U x) 0 u :=
    defSet_eq_of_carrier_eq (vfPrefixHeadFibre_carrier U x u).symm
  have hV : extendBase (coordinateFibre V 0 (vfPrefixTuple x u)) hAug = coordinateFibre (vfPrefixFibre V x) 0 u :=
    defSet_eq_of_carrier_eq (vfPrefixHeadFibre_carrier V x u).symm
  let E := T.extendBase hAug
  refine ⟨specialCastBoth E hU hV,?_⟩
  intro q
  let q0 : coordinateFibre U 0 (vfPrefixTuple x u) :=
    ⟨q.val,(Set.ext_iff.mp (vfPrefixHeadFibre_carrier U x u) q.val).mp q.property⟩
  let q1 : extendBase (coordinateFibre U 0 (vfPrefixTuple x u)) hAug := ⟨q0.val,q0.property⟩
  apply Subtype.ext
  have h2 := specialCastBoth_value E hU hV q q1 rfl
  have h1 := T.chain.extendBase_apply hAug q1
  have h0 := congrArg (fun z : coordinateFibre V 0 (vfPrefixTuple x u) => z.val) (hT q0)
  exact h2.trans (h1.trans (h0.trans (vfPrefixUnaryFibreMap_value f hi x u q).symm))

end IntegrationInACVF.Section6
