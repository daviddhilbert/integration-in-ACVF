import IntegrationSection4.RVLabelAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.GammaRVMap

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m d e : ℕ}
variable {A D : Set (Point (M := M) n m)}

def one (G : GammaParameters.Base (M := M)) (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) : GammaRVMap G A 1 :=
  ofReal G A hA (membershipMap (PresentedSet.univ (pointSpace n m) G.real)
    (PresentedSet.univ (pointSpace n m) G.real))

theorem one_apply (G : GammaParameters.Base (M := M)) (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (a : A) : (one G A hA).toFun a 0 = rv (1 : VF (M := M)) := by
  simp [one,ofReal,membershipMap,membershipPoint,Map.ofCodes]
  intro hn
  exact (hn (Set.mem_univ _)).elim

def tagLeft (P : GammaRVMap G A d) (e : ℕ) : GammaRVMap G A (1+(d+e)) :=
  (zero G A P.domain_definable 1).pair (P.pair (zero G A P.domain_definable e))

def tagRight (Q : GammaRVMap G D e) (d : ℕ) : GammaRVMap G D (1+(d+e)) :=
  (one G D Q.domain_definable).pair ((zero G D Q.domain_definable d).pair Q)

def join (P : GammaRVMap G A d) (Q : GammaRVMap G D e) (hAD : Disjoint A D) :
    GammaRVMap G (A ∪ D) (1+(d+e)) := (tagLeft P e).union (tagRight Q d) hAD

theorem left_tag (P : GammaRVMap G A d) (a : A) (e : ℕ) :
    (tagLeft P e).toFun a (Fin.castAdd (d+e) (0 : Fin 1)) = rv (0 : VF (M := M)) := by
  simp only [tagLeft,pair,Fin.append_left]
  rfl

theorem right_tag (Q : GammaRVMap G D e) (a : D) (d : ℕ) :
    (tagRight Q d).toFun a (Fin.castAdd (d+e) (0 : Fin 1)) = rv (1 : VF (M := M)) := by
  simp only [tagRight,pair,Fin.append_left]
  exact one_apply G D Q.domain_definable a

theorem zero_ne_one : rv (0 : VF (M := M)) ≠ rv (1 : VF (M := M)) := by
  intro h
  exact one_ne_zero ((rv_eq_zero_iff (1 : VF (M := M))).mp h.symm)

theorem join_left (P : GammaRVMap G A d) (Q : GammaRVMap G D e) (hAD : Disjoint A D)
    (a : A) : (join P Q hAD).toFun ⟨a.val,Or.inl a.property⟩ = (tagLeft P e).toFun a := by
  change (if h : a.val ∈ A then _ else _) = _
  rw [dif_pos a.property]

theorem join_right (P : GammaRVMap G A d) (Q : GammaRVMap G D e) (hAD : Disjoint A D)
    (a : D) : (join P Q hAD).toFun ⟨a.val,Or.inr a.property⟩ = (tagRight Q d).toFun a := by
  have hn : a.val ∉ A := fun h => Set.disjoint_left.mp hAD h a.property
  change (if h : a.val ∈ A then _ else _) = _
  rw [dif_neg hn]

theorem join_fibre_left (P : GammaRVMap G A d) (Q : GammaRVMap G D e) (hAD : Disjoint A D)
    (a : A) (b : ↥(A ∪ D))
    (he : (join P Q hAD).toFun b = (join P Q hAD).toFun ⟨a.val,Or.inl a.property⟩) : b.val ∈ A := by
  by_contra hn
  let c : D := ⟨b.val,b.property.resolve_left hn⟩
  have hright : (join P Q hAD).toFun b = (tagRight Q d).toFun c := by
    change (if h : b.val ∈ A then _ else _) = _
    rw [dif_neg hn]
  rw [hright,join_left] at he
  have hh := congrFun he (Fin.castAdd (d+e) (0 : Fin 1))
  rw [right_tag,left_tag] at hh
  exact zero_ne_one hh.symm

theorem join_fibre_right (P : GammaRVMap G A d) (Q : GammaRVMap G D e) (hAD : Disjoint A D)
    (a : D) (b : ↥(A ∪ D))
    (he : (join P Q hAD).toFun b = (join P Q hAD).toFun ⟨a.val,Or.inr a.property⟩) : b.val ∈ D := by
  by_cases hb : b.val ∈ A
  · have hleft : (join P Q hAD).toFun b = (tagLeft P e).toFun ⟨b.val,hb⟩ := by
      change (if h : b.val ∈ A then _ else _) = _
      rw [dif_pos hb]
    rw [hleft,join_right] at he
    have hh := congrFun he (Fin.castAdd (d+e) (0 : Fin 1))
    rw [left_tag,right_tag] at hh
    exact (zero_ne_one hh).elim
  · exact b.property.resolve_left hb

theorem one_toFun (G : GammaParameters.Base (M := M)) (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (a : A) :
    (one G A hA).toFun a = fun _ : Fin 1 => rv (1 : VF (M := M)) := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact one_apply G A hA a

theorem tagLeft_eq_iff (P : GammaRVMap G A d) (a b : A) (e : ℕ) :
    (tagLeft P e).toFun a = (tagLeft P e).toFun b ↔ P.toFun a = P.toFun b := by
  change (Fin.append (fun _ : Fin 1 => rv (0 : VF (M := M)))
    (Fin.append (P.toFun a) (fun _ : Fin e => rv (0 : VF (M := M)))) =
    Fin.append (fun _ : Fin 1 => rv (0 : VF (M := M)))
    (Fin.append (P.toFun b) (fun _ : Fin e => rv (0 : VF (M := M))))) ↔ _
  constructor
  · intro he
    funext i
    have hh := congrFun he (Fin.natAdd 1 (Fin.castAdd e i))
    simpa only [Fin.append_right,Fin.append_left] using hh
  · intro he
    rw [he]

theorem tagRight_eq_iff (Q : GammaRVMap G D e) (a b : D) (d : ℕ) :
    (tagRight Q d).toFun a = (tagRight Q d).toFun b ↔ Q.toFun a = Q.toFun b := by
  simp only [tagRight,pair,one_toFun]
  change (Fin.append (fun _ : Fin 1 => rv (1 : VF (M := M)))
    (Fin.append (fun _ : Fin d => rv (0 : VF (M := M))) (Q.toFun a))) =
    Fin.append (fun _ : Fin 1 => rv (1 : VF (M := M)))
    (Fin.append (fun _ : Fin d => rv (0 : VF (M := M))) (Q.toFun b)) ↔ _
  constructor
  · intro he
    funext i
    have hh := congrFun he (Fin.natAdd 1 (Fin.natAdd d i))
    simpa only [Fin.append_right] using hh
  · intro he
    rw [he]

theorem join_left_fibre (P : GammaRVMap G A d) (Q : GammaRVMap G D e) (hAD : Disjoint A D) (a : A) :
    {p | ∃ b : ↥(A ∪ D), b.val = p ∧ (join P Q hAD).toFun b =
      (join P Q hAD).toFun ⟨a.val,Or.inl a.property⟩} =
    {p | ∃ b : A, b.val = p ∧ P.toFun b = P.toFun a} := by
  ext p
  constructor
  · rintro ⟨b,hb,he⟩
    have hm := join_fibre_left P Q hAD a b he
    let c : A := ⟨b.val,hm⟩
    have hbVal : (join P Q hAD).toFun b = (tagLeft P e).toFun c := by
      change (if h : b.val ∈ A then _ else _) = _
      rw [dif_pos hm]
    rw [hbVal,join_left] at he
    exact ⟨c,hb,(tagLeft_eq_iff P c a e).mp he⟩
  · rintro ⟨b,hb,he⟩
    refine ⟨⟨b.val,Or.inl b.property⟩,hb,?_⟩
    rw [join_left,join_left]
    exact (tagLeft_eq_iff P b a e).mpr he

theorem join_right_fibre (P : GammaRVMap G A d) (Q : GammaRVMap G D e) (hAD : Disjoint A D) (a : D) :
    {p | ∃ b : ↥(A ∪ D), b.val = p ∧ (join P Q hAD).toFun b =
      (join P Q hAD).toFun ⟨a.val,Or.inr a.property⟩} =
    {p | ∃ b : D, b.val = p ∧ Q.toFun b = Q.toFun a} := by
  ext p
  constructor
  · rintro ⟨b,hb,he⟩
    have hm := join_fibre_right P Q hAD a b he
    have hn : b.val ∉ A := fun h => Set.disjoint_left.mp hAD h hm
    let c : D := ⟨b.val,hm⟩
    have hbVal : (join P Q hAD).toFun b = (tagRight Q d).toFun c := by
      change (if h : b.val ∈ A then _ else _) = _
      rw [dif_neg hn]
    rw [hbVal,join_right] at he
    exact ⟨c,hb,(tagRight_eq_iff Q c a d).mp he⟩
  · rintro ⟨b,hb,he⟩
    refine ⟨⟨b.val,Or.inr b.property⟩,hb,?_⟩
    rw [join_right,join_right]
    exact (tagRight_eq_iff Q b a d).mpr he

end IntegrationInACVF.Section4.GammaRVMap
