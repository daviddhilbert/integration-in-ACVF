import Section4.RVProductAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] {S : Set M} {a b : ℕ}

def packedProductEquiv (A : DefSet (rawRVSpace (M := M) a) S) (C : DefSet (rawRVSpace (M := M) b) S) :
    (A × C) ≃ rvProductDomain A C where
  toFun p := rvPackPair A C p.1 p.2
  invFun x := (⟨(rvUnpack A C x).val.1,(rvUnpack A C x).property.1⟩,
    ⟨(rvUnpack A C x).val.2,(rvUnpack A C x).property.2⟩)
  left_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> simp only [rvUnpack_pair]
  right_inv x := rvPack_unpack A C x

@[simp] theorem packedProductEquiv_apply (A : DefSet (rawRVSpace (M := M) a) S)
    (C : DefSet (rawRVSpace (M := M) b) S) (u : A) (v : C) :
    packedProductEquiv A C (u,v) = rvPackPair A C u v := rfl

end IntegrationInACVF.Section6
