import IntegrationSection6.VFPrefixHeadFibres

/-! The unary map of a head fibre after prefix restriction is the same
actual unary map obtained by fixing the full complementary VF tuple. -/
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

theorem vfPrefixUnaryFibreMap_value (f : Map U V) (hi : UnaryRelative f 0)
    (x : Fin n → VF (M := M)) (u : Fin (p+1) → VF (M := M))
    (q : coordinateFibre (vfPrefixFibre U x) 0 u) :
    (coordinateFibreMap (vfPrefixFibreMap f (vfPrefixRelative_of_unaryHead f hi) x) 0
      (vfPrefixFibreMap_unaryHead f hi x) u q).val =
    (coordinateFibreMap f 0 hi (vfPrefixTuple x u)
      ⟨q.val,(Set.ext_iff.mp (vfPrefixHeadFibre_carrier U x u) q.val).mp q.property⟩).val := by
  rw [coordinateFibreMap_apply,coordinateFibreMap_apply]
  change coordinateProject 0 (vfPrefixProject
    (f ⟨vfPrefixInsert x (coordinateInsert 0 u q.val),q.property⟩).val) = _
  have he : (⟨vfPrefixInsert x (coordinateInsert 0 u q.val),q.property⟩ : U) =
      ⟨coordinateInsert 0 (vfPrefixTuple x u) q.val,
        (Set.ext_iff.mp (vfPrefixHeadFibre_carrier U x u) q.val).mp q.property⟩ :=
    Subtype.ext (vfPrefixInsert_coordinateInsert x u q.val)
  rw [he]
  rfl

end IntegrationInACVF.Section6
