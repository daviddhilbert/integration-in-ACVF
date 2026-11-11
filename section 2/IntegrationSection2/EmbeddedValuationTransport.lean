import Section9.HenselianRingTransport
import Mathlib.Algebra.Field.Subfield.Basic

/-! The actual valuation ring of an embedded field is isomorphic to
the valuation ring of its field image. No algebraic extension theorem
or residue-degree equality is used in this transport. -/

set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section2.EmbeddedValuationTransport

variable {D K Γ : Type} [Field D] [Field K] [LinearOrderedCommGroupWithZero Γ]

noncomputable def ringEquiv (v : Valuation K Γ) (f : D →+* K) :
    (v.comap f).valuationSubring ≃+* (v.comap f.fieldRange.subtype).valuationSubring := by
  let e := RingHom.rangeRestrictFieldEquiv f
  refine {
    toFun x := ⟨e x.val,x.property⟩
    invFun y := ⟨e.symm y.val,?_⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x.val)
    right_inv y := Subtype.ext (e.apply_symm_apply y.val)
    map_add' x y := Subtype.ext (e.map_add x.val y.val)
    map_mul' x y := Subtype.ext (e.map_mul x.val y.val)
  }
  change v (f (e.symm y.val)) ≤ 1
  have he : f (e.symm y.val) = y.val.val := congrArg Subtype.val (e.apply_symm_apply y.val)
  rw [he]
  exact y.property

theorem henselian_iff (v : Valuation K Γ) (f : D →+* K) :
    HenselianLocalRing (v.comap f).valuationSubring ↔
      HenselianLocalRing (v.comap f.fieldRange.subtype).valuationSubring := by
  constructor
  · intro h
    letI := h
    exact SpecialTransformations.Section9.henselian_of_ringEquiv (ringEquiv v f)
  · intro h
    letI := h
    exact SpecialTransformations.Section9.henselian_of_ringEquiv (ringEquiv v f).symm

end IntegrationInACVF.Section2.EmbeddedValuationTransport
