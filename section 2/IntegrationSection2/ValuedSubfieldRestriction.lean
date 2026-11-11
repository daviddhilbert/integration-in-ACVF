import Section9.HenselianRingTransport

/-! Restricting the ambient field while retaining the entire base
subfield leaves its actual valuation ring unchanged up to an explicit
ring equivalence. This is transport only, not a henselian-extension input. -/

set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section2.ValuedSubfieldRestriction

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def fieldEquiv (C F : Subfield K) (hFC : F ≤ C) : F.comap C.subtype ≃+* F where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,hFC x.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def ringEquiv (v : Valuation K Γ) (C F : Subfield K) (hFC : F ≤ C) :
    ((v.comap C.subtype).comap (F.comap C.subtype).subtype).valuationSubring ≃+*
      (v.comap F.subtype).valuationSubring where
  toFun x := ⟨fieldEquiv C F hFC x.val,x.property⟩
  invFun x := ⟨(fieldEquiv C F hFC).symm x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem henselian_iff (v : Valuation K Γ) (C F : Subfield K) (hFC : F ≤ C) :
    HenselianLocalRing ((v.comap C.subtype).comap (F.comap C.subtype).subtype).valuationSubring ↔
      HenselianLocalRing (v.comap F.subtype).valuationSubring := by
  constructor
  · intro h
    letI := h
    exact SpecialTransformations.Section9.henselian_of_ringEquiv (ringEquiv v C F hFC)
  · intro h
    letI := h
    exact SpecialTransformations.Section9.henselian_of_ringEquiv (ringEquiv v C F hFC).symm

end IntegrationInACVF.Section2.ValuedSubfieldRestriction
