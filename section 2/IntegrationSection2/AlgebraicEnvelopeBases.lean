import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Perfect

/-! Algebraic and Galois base transport inside an actual algebraic
envelope. The new base is an actual comap subfield of that envelope. -/

set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section2.AlgebraicEnvelopeBases

variable {K : Type} [Field K] (F : Subfield K) (C : IntermediateField F K)

def baseMap (D : Subfield K) (hFD : F ≤ D) : F →+* D.comap C.toSubfield.subtype where
  toFun x := ⟨algebraMap F C x,hFD x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_mul' x y := Subtype.ext (map_mul _ x y)

theorem algebraic_comap [Algebra.IsAlgebraic F C] (D : Subfield K) (hFD : F ≤ D) :
    Algebra.IsAlgebraic (D.comap C.toSubfield.subtype) C := by
  letI := (baseMap F C D hFD).toAlgebra
  letI : IsScalarTower F (D.comap C.toSubfield.subtype) C :=
    IsScalarTower.of_algebraMap_eq' (by ext x;rfl)
  exact Algebra.IsAlgebraic.tower_top (K := F) (D.comap C.toSubfield.subtype)

theorem galois_comap [CharZero K] [IsAlgClosed C] [Algebra.IsAlgebraic F C]
    (D : Subfield K) (hFD : F ≤ D) : IsGalois (D.comap C.toSubfield.subtype) C := by
  letI := algebraic_comap F C D hFD
  letI : Normal (D.comap C.toSubfield.subtype) C := {
    isAlgebraic := Algebra.IsAlgebraic.isAlgebraic
    splits' _ := IsAlgClosed.splits _
  }
  exact { to_isSeparable := inferInstance, to_normal := inferInstance }

end IntegrationInACVF.Section2.AlgebraicEnvelopeBases
