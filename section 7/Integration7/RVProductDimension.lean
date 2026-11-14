import Integration7.VolumeAlmostEverywhere
import Section4.RVProduct

/-! Product dimension bounds from actual finite-to-one coordinate maps. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a b n : ℕ}

theorem rvDim_productDomain_le (A : DefSet (rawRVSpace (M := M) a) S)
    (B : DefSet (rawRVSpace (M := M) b) S) :
    rvDim (rvProductDomain A B) ≤ rvDim A + rvDim B := by
  obtain ⟨f, hf⟩ := rvDim_attained A
  obtain ⟨g, hg⟩ := rvDim_attained B
  let U : RVObject (M := M) S (rvDim A) := ⟨a, A, f⟩
  let V : RVObject (M := M) S (rvDim B) := ⟨b, B, g⟩
  exact (rvDim_le_iff _ _).mpr ⟨rvDim A + rvDim B, le_rfl,
    (rvProductObject U V).volume, rvProductObject_finite_volume U V hf hg⟩

theorem RVAlmostEverywhere.product_right
    {A : DefSet (rawRVSpace (M := M) a) S} (B : DefSet (rawRVSpace (M := M) b) S)
    {P : A → Prop} (hP : RVAlmostEverywhere A n P) :
    RVAlmostEverywhere (rvProductDomain A B) (n + b)
      (fun u => P (Map.prodFst A B (rvUnpack A B u))) := by
  obtain ⟨D, hDA, hd, hP⟩ := hP
  let E := rvProductDomain D B
  have hEA : E.carrier ⊆ (rvProductDomain A B).carrier := by
    rintro z ⟨p, rfl⟩
    exact ⟨⟨p.val, hDA p.property.1, p.property.2⟩, rfl⟩
  have hdim : rvDim E < n + b :=
    (rvDim_productDomain_le D B).trans_lt
      ((Nat.add_le_add_left (rvDim_le_arity B) (rvDim D)).trans_lt (Nat.add_lt_add_right hd b))
  refine ⟨E, hEA, hdim, ?_⟩
  intro u hu
  apply hP
  intro hD
  apply hu
  exact ⟨⟨(rvUnpack A B u).val, hD, (rvUnpack A B u).property.2⟩,
    congrArg (fun p : rvProductDomain A B => p.val) (rvPack_unpack A B u)⟩

end IntegrationInACVF.Section7
