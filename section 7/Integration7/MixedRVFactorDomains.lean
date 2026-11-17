module

public import Integration7.MixedRVMapGraphs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Cartesian products with a pure RV factor, packed without any new
VF coordinates. The inverse recovers the old mixed point and the RV
factor from the two literal RV blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] {S : Set M} {n a b : ℕ}

def mixedRVFactorPack (A : DefSet (rawMixedSpace (M := M) n a) S)
    (B : DefSet (rawRVSpace (M := M) b) S) :
    Map (A.prod B) (DefSet.univ (rawMixedSpace (M := M) n (a+b)) S) := by
  let X := DefSet.univ (rawVFSpace (M := M) n) S
  let R := DefSet.univ (rawRVSpace (M := M) a) S
  let T := DefSet.univ (rawRVSpace (M := M) b) S
  have h : (A.prod B).carrier ⊆ ((X.prod R).prod T).carrier :=
    fun _ _ => ⟨⟨Set.mem_univ _,Set.mem_univ _⟩,Set.mem_univ _⟩
  let G := (Map.prodAssoc X R T).comp (Map.inclusion h)
  exact (Map.prodUnivMap (Map.id X) (rvAppendMap S a b)).comp G.toUniv

@[simp] theorem mixed_rv_factor_pack_value
    (A : DefSet (rawMixedSpace (M := M) n a) S) (B : DefSet (rawRVSpace (M := M) b) S)
    (p : A.prod B) :
    (mixedRVFactorPack A B p).val = (p.val.1.1,Fin.append p.val.1.2 p.val.2) := rfl

theorem mixed_rv_factor_pack_injective
    (A : DefSet (rawMixedSpace (M := M) n a) S) (B : DefSet (rawRVSpace (M := M) b) S) :
    Function.Injective (mixedRVFactorPack A B) := by
  intro p q he
  have h := congrArg Subtype.val he
  change (p.val.1.1,Fin.append p.val.1.2 p.val.2) = (q.val.1.1,Fin.append q.val.1.2 q.val.2) at h
  have hx := congrArg Prod.fst h
  have hr : p.val.1.2=q.val.1.2 := by
    funext i
    simpa only [Fin.append_left] using congrArg (fun w => w.2 (Fin.castAdd b i)) h
  have ht : p.val.2=q.val.2 := by
    funext i
    simpa only [Fin.append_right] using congrArg (fun w => w.2 (Fin.natAdd a i)) h
  exact Subtype.ext (Prod.ext (Prod.ext hx hr) ht)

def mixedRVFactorDomain (A : DefSet (rawMixedSpace (M := M) n a) S)
    (B : DefSet (rawRVSpace (M := M) b) S) : DefSet (rawMixedSpace (M := M) n (a+b)) S :=
  (mixedRVFactorPack A B).image

theorem mixed_rv_factor_pack_to_image_bijective
    (A : DefSet (rawMixedSpace (M := M) n a) S) (B : DefSet (rawRVSpace (M := M) b) S) :
    Function.Bijective (mixedRVFactorPack A B).toImage := by
  constructor
  · intro p q h
    have hv := congrArg Subtype.val h
    exact mixed_rv_factor_pack_injective A B (Subtype.ext hv)
  · rintro ⟨p,q,hq⟩
    exact ⟨q,Subtype.ext hq⟩

def mixedRVFactorUnpack (A : DefSet (rawMixedSpace (M := M) n a) S)
    (B : DefSet (rawRVSpace (M := M) b) S) : Map (mixedRVFactorDomain A B) (A.prod B) :=
  (mixedRVFactorPack A B).toImage.inverse (mixed_rv_factor_pack_to_image_bijective A B)

@[simp] theorem mixed_rv_factor_unpack_pack
    (A : DefSet (rawMixedSpace (M := M) n a) S) (B : DefSet (rawRVSpace (M := M) b) S)
    (p : A.prod B) : mixedRVFactorUnpack A B ((mixedRVFactorPack A B).toImage p) = p :=
  Map.inverse_apply _ _ p

theorem mixed_rv_factor_unpack_value
    (A : DefSet (rawMixedSpace (M := M) n a) S) (B : DefSet (rawRVSpace (M := M) b) S)
    (p : mixedRVFactorDomain A B) :
    (mixedRVFactorUnpack A B p).val = ((p.val.1,p.val.2 ∘ Fin.castAdd b),p.val.2 ∘ Fin.natAdd a) := by
  let q := mixedRVFactorUnpack A B p
  have h := congrArg Subtype.val (Map.apply_inverse (mixedRVFactorPack A B).toImage
    (mixed_rv_factor_pack_to_image_bijective A B) p)
  change (q.val.1.1,Fin.append q.val.1.2 q.val.2) = p.val at h
  have hx := congrArg Prod.fst h
  have hr : q.val.1.2=p.val.2 ∘ Fin.castAdd b := by
    funext i
    simpa only [Fin.append_left,Function.comp_apply] using congrArg (fun w => w.2 (Fin.castAdd b i)) h
  have ht : q.val.2=p.val.2 ∘ Fin.natAdd a := by
    funext i
    simpa only [Fin.append_right,Function.comp_apply] using congrArg (fun w => w.2 (Fin.natAdd a i)) h
  exact Prod.ext (Prod.ext hx hr) ht

theorem mem_mixed_rv_factor_domain
    (A : DefSet (rawMixedSpace (M := M) n a) S) (B : DefSet (rawRVSpace (M := M) b) S)
    (x : (rawVFSpace (M := M) n).Carrier) (r : (rawRVSpace (M := M) (a+b)).Carrier) :
    (x,r) ∈ (mixedRVFactorDomain A B).carrier ↔
      (x,r ∘ Fin.castAdd b) ∈ A.carrier ∧ r ∘ Fin.natAdd a ∈ B.carrier := by
  constructor
  · intro hp
    let p : mixedRVFactorDomain A B := ⟨(x,r),hp⟩
    have hv := mixed_rv_factor_unpack_value A B p
    have h := (mixedRVFactorUnpack A B p).property
    change (mixedRVFactorUnpack A B p).val.1 ∈ A.carrier ∧
      (mixedRVFactorUnpack A B p).val.2 ∈ B.carrier at h
    exact Eq.mp (congrArg (fun w => w.1 ∈ A.carrier ∧ w.2 ∈ B.carrier) hv) h
  · rintro ⟨hA,hB⟩
    refine ⟨⟨((x,r ∘ Fin.castAdd b),r ∘ Fin.natAdd a),hA,hB⟩,?_⟩
    exact Prod.ext rfl Fin.append_castAdd_natAdd

end IntegrationInACVF.Section7
