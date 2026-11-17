module

public import Section4.MixedProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual inverse Cartesian-product chart recovers the two
literal VF and RV blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] {S : Set M} {n a m b : ℕ}

theorem mixed_product_unpack_value
    (A : DefSet (rawMixedSpace (M := M) n a) S) (B : DefSet (rawMixedSpace (M := M) m b) S)
    (q : mixedProductDomain A B) :
    (mixedUnpack A B q).val =
      ((q.val.1 ∘ Fin.castAdd m,q.val.2 ∘ Fin.castAdd b),
        (q.val.1 ∘ Fin.natAdd n,q.val.2 ∘ Fin.natAdd a)) := by
  let p := mixedUnpack A B q
  have h := congrArg Subtype.val (mixedPack_unpack A B q)
  change (Fin.append (m := n) (n := m) p.val.1.1 p.val.2.1,
    Fin.append (m := a) (n := b) p.val.1.2 p.val.2.2)=q.val at h
  have hx : p.val.1.1=q.val.1 ∘ Fin.castAdd m := by
    funext i
    simpa only [Fin.append_left,Function.comp_apply] using congrArg (fun w => w.1 (Fin.castAdd m i)) h
  have hr : p.val.1.2=q.val.2 ∘ Fin.castAdd b := by
    funext i
    simpa only [Fin.append_left,Function.comp_apply] using congrArg (fun w => w.2 (Fin.castAdd b i)) h
  have hy : p.val.2.1=q.val.1 ∘ Fin.natAdd n := by
    funext i
    simpa only [Fin.append_right,Function.comp_apply] using congrArg (fun w => w.1 (Fin.natAdd n i)) h
  have hs : p.val.2.2=q.val.2 ∘ Fin.natAdd a := by
    funext i
    simpa only [Fin.append_right,Function.comp_apply] using congrArg (fun w => w.2 (Fin.natAdd a i)) h
  exact Prod.ext (Prod.ext hx hr) (Prod.ext hy hs)

end IntegrationInACVF.Section7
