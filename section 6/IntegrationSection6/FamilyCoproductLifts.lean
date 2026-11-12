import IntegrationSection6.DefinableFamilyLifts
import IntegrationSection6.GammaRawCoproductSchemata
import IntegrationSection6.GammaTaggedLifts
import IntegrationSection6.GammaVFAllAdditivePresentation
import IntegrationSection6.GammaVFAllScissorDomains
import IntegrationSection6.GammaMixedEmptyIsomorphisms

/-! A family coproduct has the literal disjoint union of tagged total
lifts. The resulting additive identity holds in the actual VF scissors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem familyLiftDomain_coprod (A : Set (Point (M := M) p 0))
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b k) :
    familyLiftDomain A (F.coprodFormula G) =
      taggedLeftSet (familyLiftDomain A F) b ∪ taggedRightSet (familyLiftDomain A G) a := by
  ext q
  have hv := F.coprod_row_volume_formula G (fun j => (q.1 (Fin.castAdd k j)).val)
    (fun j => (q.1 (Fin.castAdd k j)).property) q.2 (tupleRV (q.1 ∘ Fin.natAdd p))
  constructor
  · intro h
    rcases hv.mp h.2 with ⟨r,hr,he⟩ | ⟨r,hr,he⟩
    · exact Or.inl ⟨⟨(q.1,r),h.1,hr⟩,Prod.ext rfl he⟩
    · exact Or.inr ⟨⟨(q.1,r),h.1,hr⟩,Prod.ext rfl he⟩
  · rintro (⟨u,he⟩ | ⟨u,he⟩)
    · have hq := congrArg Prod.fst he
      have hr := congrArg Prod.snd he
      refine ⟨?_,hv.mpr (Or.inl ⟨u.val.2,?_,hr⟩)⟩
      · exact hq ▸ u.property.1
      · exact hq ▸ u.property.2
    · have hq := congrArg Prod.fst he
      have hr := congrArg Prod.snd he
      refine ⟨?_,hv.mpr (Or.inr ⟨u.val.2,?_,hr⟩)⟩
      · exact hq ▸ u.property.1
      · exact hq ▸ u.property.2

theorem taggedLeftSet_finite {n m r : ℕ} (A : Set (Point (M := M) n m))
    (hf : ∀ x, {t | (x,t) ∈ A}.Finite) : ∀ x, {t | (x,t) ∈ taggedLeftSet A r}.Finite := by
  intro x
  apply ((hf x).image (@rvLeftTag M N hN m r)).subset
  rintro t ⟨u,he⟩
  have hx : u.val.1 = x := congrArg Prod.fst he
  refine ⟨u.val.2,?_,congrArg Prod.snd he⟩
  change (x,u.val.2) ∈ A
  exact hx ▸ u.property

theorem taggedRightSet_finite {n m r : ℕ} (A : Set (Point (M := M) n r))
    (hf : ∀ x, {t | (x,t) ∈ A}.Finite) : ∀ x, {t | (x,t) ∈ taggedRightSet A m}.Finite := by
  intro x
  apply ((hf x).image (@rvRightTag M N hN r m)).subset
  rintro t ⟨u,he⟩
  have hx : u.val.1 = x := congrArg Prod.fst he
  refine ⟨u.val.2,?_,congrArg Prod.snd he⟩
  change (x,u.val.2) ∈ A
  exact hx ▸ u.property

theorem gammaVFAll_disjoint_union {n m : ℕ} (U V : Set (Point (M := M) n m))
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V)
    (fU : ∀ x, {t | (x,t) ∈ U}.Finite) (fV : ∀ x, {t | (x,t) ∈ V}.Finite) (hd : Disjoint U V) :
    PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B)
      (⟨(n,m),U ∪ V,(gammaLogicInput B).union hU hV,fun x => (fU x).union (fV x)⟩ : GammaVFAllFiniteObject B) =
    PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) ⟨(n,m),U,hU,fU⟩ +
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) ⟨(n,m),V,hV,fV⟩ := by
  have hs := PositiveAdditiveGrothendieck.of_scissor (gammaVFAllAdditivePresentation B)
    ((gammaVFAllScissor_domains U V (U ∪ V) (U ∩ V) hU hV ((gammaLogicInput B).union hU hV)
      ((gammaLogicInput B).inter hU hV) fU fV (fun x => (fU x).union (fV x))
      (fun x => (fU x).subset (fun _ h => h.1))).mpr ⟨rfl,rfl⟩)
  have hz : PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B)
      (⟨(n,m),U ∩ V,(gammaLogicInput B).inter hU hV,fun x => (fU x).subset (fun _ h => h.1)⟩ : GammaVFAllFiniteObject B) = 0 :=
    (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) (b := gammaVFAllEmpty B) ⟨gammaEmptyMixedIso (Set.disjoint_iff_inter_eq_empty.mp hd) rfl⟩).trans
      (PositiveAdditiveGrothendieck.of_empty _)
  rw [hz,add_zero] at hs
  exact hs.symm

end IntegrationInACVF.Section6
