import IntegrationSection5.RelativeSpecialRestriction

/-! Retagging the endpoints of an actual special bijection by equal
presented sets changes neither its point values nor its geometric chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}
variable {U U' : DefSet (M := M) S n a} {V V' : DefSet (M := M) S n b}

def specialCastBoth (T : SpecialBijection U V) (hU : U = U') (hV : V = V') : SpecialBijection U' V' :=
  hU ▸ hV ▸ T

theorem specialCastBoth_value (T : SpecialBijection U V) (hU : U = U') (hV : V = V')
    (u' : U') (u : U) (hu : u'.val = u.val) :
    ((specialCastBoth T hU hV).toMap u').val = (T.toMap u).val := by
  cases hU
  cases hV
  have he : u' = u := Subtype.ext hu
  rw [he]
  rfl

end IntegrationInACVF.Section6
