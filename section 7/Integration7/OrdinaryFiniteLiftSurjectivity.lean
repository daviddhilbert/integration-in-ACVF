import Integration7.FiniteCategoryStructureTransport
import Section5.Surjectivity

/-! The predecessor's actual finite lift presentation transfers from
normalization to the original canonical structure, over the same base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem ordinary_finite_lift_presentation_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : VFFiniteObject (rawRVSpace (M := M) 1) (C.base : Set M) n) :
    ∃ U : RVFiniteObject (M := M) (C.base : Set M) n,
      Nonempty (A ≅ rvLiftFiniteObject (rawRVSpace (M := M) 1) U) := by
  let N := @CanonicalStructure.normalize M sM
  letI : LRV.Structure M := sM
  have hN : N = sM := normalize_eq_of_isCanonical hc
  let E := vfFiniteStructureEquiv hN (C.base : Set M) n
  let R := rvFiniteStructureEquiv hN (C.base : Set M) n
  obtain ⟨U,⟨e⟩⟩ := SpecialTransformations.Section5.corollary_5_7_finite_of_rvCoded
    C.uncountable.le C.saturated C.model00 C.small (@rawRVSpace M N 1) (@rawRVSpace_rvCoded M N 1)
    n (E.inverse.obj A)
  refine ⟨R.functor.obj U,⟨?_⟩⟩
  exact (E.counitIso.app A).symm.trans ((E.functor.mapIso e).trans
    (eqToIso (finite_structure_transport_lift hN (@CanonicalStructure.normalized_model M sM hM) hM U)))

end IntegrationInACVF.Section7
