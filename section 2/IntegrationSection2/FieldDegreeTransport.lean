import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Field-degree transport under two actual field isomorphisms with
compatible scalar multiplication. -/

namespace IntegrationInACVF.Section2.FieldDegreeTransport

variable {F E L N : Type} [Field F] [Field E] [Field L] [Field N]
  [Algebra F L] [Algebra E N]

theorem finrank (eF : F ≃+* E) (eL : L ≃+* N)
    (h : ∀ c x, eL (c • x) = eF c • eL x) :
    Module.finrank F L = Module.finrank E N :=
  congrArg Cardinal.toNat (rank_eq_of_equiv_equiv eF eL.toAddEquiv eF.bijective h)

theorem finite_left (eF : F ≃+* E) (eL : L ≃+* N)
    (h : ∀ c x, eL (c • x) = eF c • eL x) [FiniteDimensional E N] :
    FiniteDimensional F L :=
  FiniteDimensional.of_finrank_pos (by
    rw [finrank eF eL h]
    exact Module.finrank_pos)

end IntegrationInACVF.Section2.FieldDegreeTransport
