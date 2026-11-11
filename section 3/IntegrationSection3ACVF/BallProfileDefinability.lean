import IntegrationSection3ACVF.FullBallCoset
import IntegrationSection3.ImaginaryBaseRanges
import IntegrationSection3.FiniteBallProfiles

/-! Intrinsic membership profiles of a full-base definable ball family.
No point of a finite hitting set is named in these definitions. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.FiniteBallProfiles

namespace IntegrationInACVF.Section3ACVF.BallProfileDefinability

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def leProfile (T : Set (BallImaginaries.Ball M)) (x y : M) : Prop :=
  profile T BallImaginaries.underlying x ⊆ profile T BallImaginaries.underlying y

theorem leProfile_definable (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T) :
    FullBaseAtomicity.OverBase B {z : Fin 2 → M | leProfile T (z 0) (z 1)} := by
  let q := @BallPresentation.presentation M sM hM
  have hm : FullBaseAtomicity.Relation B BallImaginaries.underlying :=
    FullBaseAtomicity.OverBase.of_real (BallPresentation.membership_definable B.real)
  let πx : Fin 4 ⊕ Fin 1 → Fin 2 ⊕ Fin 4 := Sum.elim Sum.inr (fun _ => .inl 0)
  let πy : Fin 4 ⊕ Fin 1 → Fin 2 ⊕ Fin 4 := Sum.elim Sum.inr (fun _ => .inl 1)
  have h := FullBaseAtomicity.OverBase.forall_block
    ((hT.preimage_comp (Sum.inr : Fin 4 → Fin 2 ⊕ Fin 4)).inter
      ((hm.preimage_comp πx).inter (hm.preimage_comp πy).compl)).compl
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  change (∀ c : Fin 4 → M,
    ¬ ((∃ hc : c ∈ q.codes, q.decode ⟨c,hc⟩ ∈ T) ∧
      (∃ hc : c ∈ q.codes, z 0 ∈ BallImaginaries.underlying (q.decode ⟨c,hc⟩)) ∧
      ¬ ∃ hc : c ∈ q.codes, z 1 ∈ BallImaginaries.underlying (q.decode ⟨c,hc⟩))) ↔ _
  constructor
  · intro h i hi
    refine ⟨hi.1,?_⟩
    obtain ⟨c,hc⟩ := q.onto i
    by_contra hy
    apply h c.val
    refine ⟨⟨c.property,hc.symm ▸ hi.1⟩,⟨c.property,hc.symm ▸ hi.2⟩,?_⟩
    rintro ⟨_,hyc⟩
    exact hy (hc ▸ hyc)
  · intro h c
    rintro ⟨⟨hc,ht⟩,⟨_,hx⟩,hy⟩
    exact hy ⟨hc,(h ⟨ht,hx⟩).2⟩

theorem terminal_definable (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T) :
    FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | IsTerminal T BallImaginaries.underlying (z 0)} := by
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hm : FullBaseAtomicity.Relation B BallImaginaries.underlying :=
    FullBaseAtomicity.OverBase.of_real (BallPresentation.membership_definable B.real)
  have hne : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | ∃ i ∈ T, z 0 ∈ BallImaginaries.underlying i} := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryBaseFamilies.Relation.range (ImaginaryBaseFamilies.Relation.restrict hp hT hm)
  have hR := leProfile_definable B T hT
  let π : Fin 2 → Fin 1 ⊕ Fin 1 := ![.inl 0,.inr 0]
  have hall := FullBaseAtomicity.OverBase.forall_block
    ((hR.compl.union (hR.preimage_comp (![1,0] : Fin 2 → Fin 2))).preimage_comp π)
  apply FullBaseAtomicity.OverBase.congr (hne.inter hall)
  intro z
  change ((∃ i ∈ T, z 0 ∈ BallImaginaries.underlying i) ∧
    ∀ y : Fin 1 → M, ¬ leProfile T (z 0) (y 0) ∨ leProfile T (y 0) (z 0)) ↔ _
  constructor
  · rintro ⟨⟨i,hi,hxi⟩,hall⟩
    exact ⟨⟨i,hi,hxi⟩,fun y hy => (hall ![y]).resolve_left (fun hn => hn hy)⟩
  · rintro ⟨⟨i,hi,hxi⟩,hall⟩
    refine ⟨⟨i,hi,hxi⟩,fun y => ?_⟩
    by_cases hy : leProfile T (z 0) (y 0)
    · exact Or.inr (hall (y 0) hy)
    · exact Or.inl hy

theorem class_definable (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T) :
    FullBaseAtomicity.OverBase B
      {z : Fin 2 → M | z 1 ∈ profileClass T BallImaginaries.underlying (z 0)} := by
  have hR := leProfile_definable B T hT
  apply FullBaseAtomicity.OverBase.congr (hR.inter (hR.preimage_comp (![1,0] : Fin 2 → Fin 2)))
  intro z
  exact ⟨fun h => Set.Subset.antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩

def terminalBalls (T : Set (BallImaginaries.Ball M)) : Set (BallImaginaries.Ball M) :=
  {i | ∃ x, IsTerminal T BallImaginaries.underlying x ∧
    BallImaginaries.underlying i = profileClass T BallImaginaries.underlying x}

theorem terminalBalls_definable (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T) :
    FullBaseAtomicity.Family B (terminalBalls T) := by
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm : FullBaseAtomicity.Relation B BallImaginaries.underlying :=
    FullBaseAtomicity.OverBase.of_real (BallPresentation.membership_definable B.real)
  let D : Set M := {x | IsTerminal T BallImaginaries.underlying x}
  let R : Set (M × M) := {xy | xy.2 ∈ profileClass T BallImaginaries.underlying xy.1}
  have ht : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ D} := terminal_definable B T hT
  have he : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R} := class_definable B T hT
  letI := @CanonicalStructure.normalize M sM
  exact ImaginaryBaseFamilies.rangeFamily_definable (p := p) (q := q)
    (D := D) (R := R) hp hq hm ht he

omit hM in
theorem terminalBalls_disjoint (T : Set (BallImaginaries.Ball M)) :
    (terminalBalls T).Pairwise (fun i j =>
      Disjoint (BallImaginaries.underlying i) (BallImaginaries.underlying j)) := by
  intro i hi j hj hne
  obtain ⟨x,_,hi⟩ := hi
  obtain ⟨y,_,hj⟩ := hj
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hzx : profile T BallImaginaries.underlying z = profile T BallImaginaries.underlying x :=
    (Set.ext_iff.mp hi z).mp hzi
  have hzy : profile T BallImaginaries.underlying z = profile T BallImaginaries.underlying y :=
    (Set.ext_iff.mp hj z).mp hzj
  have he : profileClass T BallImaginaries.underlying x = profileClass T BallImaginaries.underlying y := by
    ext w
    change (profile T BallImaginaries.underlying w = profile T BallImaginaries.underlying x) ↔
      (profile T BallImaginaries.underlying w = profile T BallImaginaries.underlying y)
    rw [hzx.symm.trans hzy]
  exact hne (BallImaginaries.underlying_injective (hi.trans (he.trans hj.symm)))

end IntegrationInACVF.Section3ACVF.BallProfileDefinability
