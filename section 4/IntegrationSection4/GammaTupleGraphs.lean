import IntegrationSection4.GammaBaseDescent
import Section5.GammaInvariantLogic

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaTupleGraphs

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem point_sorted {n m : ℕ} (p : Point (M := M) n m) :
    ∀ i, sortEval (gammaPointSort n m i) (gammaPointCode p i) := by
  intro i
  cases i using Fin.addCases with
  | left i => simpa only [gammaPointSort,gammaPointCode,Fin.append_left,sortEval,iVF] using (vfAt p i).property
  | right i => simpa only [gammaPointSort,gammaPointCode,Fin.append_right,sortEval,iRV] using (p.2 i).property

theorem point_onto {n m : ℕ} (z : Fin (n+m) → M)
    (hz : ∀ i, sortEval (gammaPointSort n m i) (z i)) :
    ∃ p : Point (M := M) n m, gammaPointCode p = z := by
  let p : Point (M := M) n m :=
    (fun i => ⟨z (Fin.castAdd m i),by simpa only [gammaPointSort,Fin.append_left,sortEval,iVF] using hz (Fin.castAdd m i)⟩,
      fun i => ⟨z (Fin.natAdd n i),by simpa only [gammaPointSort,Fin.append_right,sortEval,iRV] using hz (Fin.natAdd n i)⟩)
  refine ⟨p,?_⟩
  funext i
  cases i using Fin.addCases with
  | left i => simp only [gammaPointCode,Fin.append_left]; rfl
  | right i => simp only [gammaPointCode,Fin.append_right]; rfl

theorem code_injective {n m : ℕ} :
    Function.Injective (gammaPointCode (M := M) (n := n) (m := m)) := by
  intro p q he
  apply Prod.ext
  · funext i
    apply Subtype.ext
    have hh := congrFun he (Fin.castAdd m i)
    simpa only [gammaPointCode,Fin.append_left,vfAt] using hh
  · funext i
    apply Subtype.ext
    have hh := congrFun he (Fin.natAdd n i)
    simpa only [gammaPointCode,Fin.append_right] using hh

def rawGraph {n m u w : ℕ}
    (r : Point (M := M) n m → Point (M := M) u w → Prop) :
    Set (Fin ((n+m)+(u+w)) → M) :=
  {z | ∃ p q, r p q ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = z}

theorem rawGraph_definable (G : GammaParameters.Base (M := M)) {n m u w : ℕ}
    (r : Point (M := M) n m → Point (M := M) u w → Prop) (hr : GammaGraphDefinable G r) :
    FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) (rawGraph r) :=
  GammaBaseBridge.of_gamma G hr

theorem rawGraph_iff {n m u w : ℕ}
    (r : Point (M := M) n m → Point (M := M) u w → Prop)
    (p : Point (M := M) n m) (q : Point (M := M) u w) :
    Fin.append (gammaPointCode p) (gammaPointCode q) ∈ rawGraph r ↔ r p q := by
  constructor
  · rintro ⟨a,b,hr,he⟩
    have hp : gammaPointCode a = gammaPointCode p := by
      funext i
      have hh := congrFun he (Fin.castAdd (u+w) i)
      simpa only [Fin.append_left] using hh
    have hq : gammaPointCode b = gammaPointCode q := by
      funext i
      have hh := congrFun he (Fin.natAdd (n+m) i)
      simpa only [Fin.append_right] using hh
    exact code_injective hp ▸ code_injective hq ▸ hr
  · intro hr
    exact ⟨p,q,hr,rfl⟩

theorem rawGraph_left_iff {n m u w : ℕ}
    (r : Point (M := M) n m → Point (M := M) u w → Prop)
    (z : Fin (n+m) → M) (q : Point (M := M) u w) :
    Fin.append z (gammaPointCode q) ∈ rawGraph r ↔
      ∃ p : Point (M := M) n m, gammaPointCode p = z ∧ r p q := by
  constructor
  · rintro ⟨a,b,hr,he⟩
    have hp : gammaPointCode a = z := by
      funext i
      have hh := congrFun he (Fin.castAdd (u+w) i)
      simpa only [Fin.append_left] using hh
    have hq : gammaPointCode b = gammaPointCode q := by
      funext i
      have hh := congrFun he (Fin.natAdd (n+m) i)
      simpa only [Fin.append_right] using hh
    exact ⟨a,hp,code_injective hq ▸ hr⟩
  · rintro ⟨p,hp,hr⟩
    exact ⟨p,q,hr,by rw [hp]⟩

theorem of_full (G : GammaParameters.Base (M := M)) {n m u w : ℕ}
    (R : Set (Fin ((n+m)+(u+w)) → M))
    (hR : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) R)
    (hProper : ∀ z ∈ R, ∀ i,
      sortEval (Fin.append (gammaPointSort n m) (gammaPointSort u w) i) (z i)) :
    GammaGraphDefinable G (fun (p : Point (M := M) n m) (q : Point (M := M) u w) =>
      Fin.append (gammaPointCode p) (gammaPointCode q) ∈ R) := by
  have hEq : {z | ∃ (p : Point (M := M) n m) (q : Point (M := M) u w),
      Fin.append (gammaPointCode p) (gammaPointCode q) ∈ R ∧
        Fin.append (gammaPointCode p) (gammaPointCode q) = z} = R := by
    ext z
    constructor
    · rintro ⟨p,q,h,rfl⟩
      exact h
    · intro hz
      let a : Fin (n+m) → M := fun i => z (Fin.castAdd (u+w) i)
      let b : Fin (u+w) → M := fun i => z (Fin.natAdd (n+m) i)
      have ha : ∀ i, sortEval (gammaPointSort n m i) (a i) := by
        intro i
        simpa only [Fin.append_left] using hProper z hz (Fin.castAdd (u+w) i)
      have hb : ∀ i, sortEval (gammaPointSort u w i) (b i) := by
        intro i
        simpa only [Fin.append_right] using hProper z hz (Fin.natAdd (n+m) i)
      obtain ⟨p,hp⟩ := point_onto a ha
      obtain ⟨q,hq⟩ := point_onto b hb
      have he : Fin.append (gammaPointCode p) (gammaPointCode q) = z := by
        rw [hp,hq]
        funext i
        cases i using Fin.addCases with
        | left i => simp only [Fin.append_left]; rfl
        | right i => simp only [Fin.append_right]; rfl
      exact ⟨p,q,he.symm ▸ hz,he⟩
  change DefinableOverBase G _ _
  rw [hEq]
  exact GammaBaseDescent.to_gamma G _ R hR hProper

/-- Raw relations need no external properness assumption: intersect with
the sort chart internally, which has no effect on actual mixed points. -/
theorem relation_of_full (G : GammaParameters.Base (M := M)) {n m u w : ℕ}
    (R : Set (Fin ((n+m)+(u+w)) → M))
    (hR : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) R) :
    GammaGraphDefinable G (fun (p : Point (M := M) n m) (q : Point (M := M) u w) =>
      Fin.append (gammaPointCode p) (gammaPointCode q) ∈ R) := by
  let sn := Fin.append (gammaPointSort n m) (gammaPointSort u w)
  have hSort : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G)
      {z : Fin ((n+m)+(u+w)) → M | ∀ i, sortEval (sn i) (z i)} :=
    FullBaseAtomicity.OverBase.of_real
      (@SpecialTransformations.Section4.tuple_domain_definable M sM hM G.real
        (Fin ((n+m)+(u+w))) inferInstance sn)
  have h := of_full G _ (FullBaseAtomicity.OverBase.inter hSort hR) (fun _ hz => hz.1)
  apply GammaGraphDefinable.congr h
  intro p q
  change ((∀ i, sortEval (sn i) (Fin.append (gammaPointCode p) (gammaPointCode q) i)) ∧ _) ↔ _
  have hp : ∀ i, sortEval (sn i) (Fin.append (gammaPointCode p) (gammaPointCode q) i) := by
    intro i
    cases i using Fin.addCases with
    | left i => simpa only [sn,Fin.append_left] using point_sorted p i
    | right i => simpa only [sn,Fin.append_right] using point_sorted q i
  exact and_iff_right hp

theorem set_of_full (G : GammaParameters.Base (M := M)) {n m : ℕ}
    (A : Set (Fin (n+m) → M))
    (hA : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) A) :
    GammaSetDefinable G {p : Point (M := M) n m | gammaPointCode p ∈ A} := by
  let sn := gammaPointSort n m
  let R := {z : Fin (n+m) → M | (∀ i, sortEval (sn i) (z i)) ∧ z ∈ A}
  have hSort : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G)
      {z : Fin (n+m) → M | ∀ i, sortEval (sn i) (z i)} :=
    FullBaseAtomicity.OverBase.of_real
      (@SpecialTransformations.Section4.tuple_domain_definable M sM hM G.real
        (Fin (n+m)) inferInstance sn)
  have hR := GammaBaseDescent.to_gamma G sn R (FullBaseAtomicity.OverBase.inter hSort hA) (fun _ hz => hz.1)
  have he : gammaPointCode '' {p : Point (M := M) n m | gammaPointCode p ∈ A} = R := by
    ext z
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨point_sorted p,hp⟩
    · rintro ⟨hz,hA⟩
      obtain ⟨p,rfl⟩ := point_onto z hz
      exact ⟨p,hA,rfl⟩
  change DefinableOverBase G sn _
  rw [he]
  exact hR

end IntegrationInACVF.Section4.GammaTupleGraphs
