import IntegrationSection4.TranslationOffsets
import Section5.GammaInvariantLogic

/-! Original-Gamma-base graph descent for the actual offset in Lemma 4.1.
The real presentation of a special bijection is internal; its invariant
chain certificates supply the complete graph over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.GammaOffsets

open TranslationOffsets

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def dropRVMap (S : Set M) (n m : ℕ) :
    Map (PresentedSet.univ (pointSpace n m) S) (PresentedSet.univ (pointSpace n 0) S) :=
  Map.ofCodes _ (fun p => (p.1, Fin.elim0))
    (fun z => Sum.elim (z ∘ Sum.inl) Fin.elim0)
    (by intro i; cases i with
        | inl i => exact rawProj S (Sum.inl i : Fin n ⊕ Fin m)
        | inr i => exact i.elim0)
    (by intro c; exact ⟨c.property.1, fun i => i.elim0⟩)
    (by
      intro c
      apply Prod.ext
      · funext i; apply Subtype.ext; rfl
      · exact Subsingleton.elim _ _)

def dropVFMap (S : Set M) (n m : ℕ) :
    Map (PresentedSet.univ (pointSpace n m) S) (PresentedSet.univ (pointSpace 0 m) S) :=
  Map.ofCodes _ (fun p => (Fin.elim0, p.2))
    (fun z => Sum.elim Fin.elim0 (z ∘ Sum.inr))
    (by intro i; cases i with
        | inl i => exact i.elim0
        | inr i => exact rawProj S (Sum.inr i : Fin n ⊕ Fin m))
    (by intro c; exact ⟨fun i => i.elim0, c.property.2⟩)
    (by
      intro c
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · funext i; apply Subtype.ext; rfl)

def vfPointMap (S : Set M) :
    Map (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)
      (PresentedSet.univ (pointSpace 1 0) S) :=
  Map.ofCodes _ (fun p => (p, Fin.elim0))
    (fun z => Sum.elim z Fin.elim0)
    (by intro i; cases i with
        | inl i => exact rawProj S i
        | inr i => exact i.elim0)
    (by intro c; exact ⟨c.property, fun i => i.elim0⟩)
    (by
      intro c
      apply Prod.ext
      · funext i; apply Subtype.ext; rfl
      · exact Subsingleton.elim _ _)

def offsetPairMap (S : Set M) (l : ℕ) :
    Map (PresentedSet.univ (spaceProd (pointSpace 1 l) (SpecialTransformations.Section4.vfSpace 1)) S)
      (PresentedSet.univ (spaceProd (pointSpace 0 l) (pointSpace 1 0)) S) := by
  let H := PresentedSet.univ (spaceProd (pointSpace (M := M) 1 l)
    (SpecialTransformations.Section4.vfSpace 1)) S
  let q := @SpecialTransformations.DefinableGeometry.Map.fst LRV M (CanonicalStructure.normalize (M := M))
    (pointSpace 1 l) (SpecialTransformations.Section4.vfSpace 1) S H
  let x := @SpecialTransformations.DefinableGeometry.Map.snd LRV M (CanonicalStructure.normalize (M := M))
    (pointSpace 1 l) (SpecialTransformations.Section4.vfSpace 1) S H
  let own := Map.comp (@SpecialTransformations.DefinableGeometry.Map.fst LRV M
    (CanonicalStructure.normalize (M := M)) (SpecialTransformations.Section4.vfSpace 1)
    (SpecialTransformations.Section4.rvSpace l) S _) q
  let inverse := Map.comp (vfPointMap S) x
  let diff := Map.comp (subtractMap 0 _) (Map.pair inverse own)
  exact Map.comp (Map.inclusion (Set.subset_univ _))
    (Map.pair (Map.comp (dropVFMap S 1 l) q) diff)

theorem offsetPairMap_apply (S : Set M) (l : ℕ) (p : Point (M := M) 1 l) (x : VF (M := M)) :
    (offsetPairMap S l ⟨(p, ![x]), Set.mem_univ _⟩).val =
      ((Fin.elim0, p.2), (![x - vfAt p 0], Fin.elim0)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i; fin_cases i; rfl
    · exact Subsingleton.elim _ _

variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem inverse_scalar_graph (T : SpecialBijection A B)
    (hT : GammaChainDefinable G T.chain) :
    GammaScalarGraphDefinable G
      (fun p x => ∃ b : B, b.val = p ∧ vfAt (T.inverseMap b).val 0 = x) := by
  let hΓ := gammaLogicInput G
  have h := hΓ.comp_graph (gamma_inverse_graph hΓ T hT)
    (hΓ.real_map_graph (dropRVMap G.real 1 m))
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨z, ⟨b, hb, hz⟩, ⟨u, hu, hq⟩⟩
    refine ⟨b, hb, ?_⟩
    have he := congrArg (fun z : Point (M := M) 1 0 => vfAt z 0) hq
    change vfAt u.val 0 = vfAt q 0 at he
    exact (congrArg (fun z : Point (M := M) 1 m => vfAt z 0) (hz.trans hu.symm)).trans he
  · rintro ⟨b, hb, he⟩
    refine ⟨(T.inverseMap b).val, ⟨b, hb, rfl⟩,
      ⟨(T.inverseMap b).val, Set.mem_univ _⟩, rfl, ?_⟩
    apply Prod.ext
    · funext i
      fin_cases i
      exact he
    · exact Subsingleton.elim _ _

def offsetGraph (T : SpecialBijection A B)
    (u : Point (M := M) 0 l) (z : Point (M := M) 1 0) : Prop :=
  ∃ b : B, u.2 = b.val.2 ∧ vfAt z 0 = offsetValue T (toLabels B b)

theorem offsetGraph_iff (T : SpecialBijection A B)
    (u : Point (M := M) 0 l) (z : Point (M := M) 1 0) :
    offsetGraph T u z ↔ ∃ t : labelsImage B, t.val = u.2 ∧ vfAt z 0 = offsetValue T t := by
  constructor
  · rintro ⟨b,hu,hz⟩
    exact ⟨toLabels B b,hu.symm,hz⟩
  · rintro ⟨t,ht,hz⟩
    obtain ⟨b,hb⟩ := t.property
    change b.val.2 = t.val at hb
    have hbt : toLabels B b = t := Subtype.ext hb
    exact ⟨b,ht.symm.trans hb.symm,hbt.symm ▸ hz⟩

theorem offsetGraph_definable (T : SpecialBijection A B)
    (hT : GammaChainDefinable G T.chain) : GammaGraphDefinable G (offsetGraph T) := by
  have h := (gammaLogicInput G).scalar_image_graph (inverse_scalar_graph T hT) (offsetPairMap G.real l)
  apply GammaGraphDefinable.congr h
  intro u z
  constructor
  · rintro ⟨p, x, ⟨b, hb, hx⟩, he⟩
    rw [offsetPairMap_apply] at he
    have hu := congrArg (fun q => q.1.2) he
    have hz := congrArg (fun q : Point (M := M) 0 l × Point (M := M) 1 0 => vfAt q.2 0) he
    refine ⟨b, hu.symm.trans (congrArg Prod.snd hb).symm, ?_⟩
    change x - vfAt p 0 = vfAt z 0 at hz
    rw [offsetValue_eq]
    have hpvf := congrArg (fun p : Point (M := M) 1 l => vfAt p 0) hb
    rw [← hpvf, ← hx] at hz
    exact hz.symm
  · rintro ⟨b, hu, hz⟩
    refine ⟨b.val, vfAt (T.inverseMap b).val 0, ⟨b, rfl, rfl⟩, ?_⟩
    rw [offsetPairMap_apply]
    apply Prod.ext
    · exact Prod.ext (Subsingleton.elim _ _) hu.symm
    · apply Prod.ext
      · funext i
        fin_cases i
        exact (offsetValue_eq T b).symm.trans hz.symm
      · exact Subsingleton.elim _ _

theorem offset_function_graph (T : SpecialBijection A B)
    (hT : GammaChainDefinable G T.chain) :
    GammaGraphDefinable G (fun (u : Point (M := M) 0 l) (z : Point (M := M) 1 0) =>
      ∃ t : labelsImage B, t.val = u.2 ∧ vfAt z 0 = offsetValue T t) :=
  GammaGraphDefinable.congr (offsetGraph_definable T hT) (offsetGraph_iff T)

/-- Lemma 4.1 with an actual same-base Gamma graph certificate; no
Gamma-logic interface or representative-definability premise is assumed. -/
theorem lemma_4_1 (T : SpecialBijection A B) (hT : GammaChainDefinable G T.chain)
    (hB : IsRVPullback (carrier B)) :
    GammaGraphDefinable G (fun (u : Point (M := M) 0 l) (z : Point (M := M) 1 0) =>
      ∃ t : labelsImage B, t.val = u.2 ∧ vfAt z 0 = offsetValue T t) ∧
      ∀ b : B,
        (fun p : Point (M := M) 1 m => vfAt p 0) '' T.inverseFibre b =
          (fun x => x + offsetValue T (toLabels B b)) ''
            {x : VF (M := M) | rv x = rv (vfAt b.val 0)} :=
  ⟨offset_function_graph T hT, inverse_fibre_translate T hB⟩

end IntegrationInACVF.Section4.GammaOffsets
