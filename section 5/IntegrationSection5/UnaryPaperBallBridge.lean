import IntegrationSection5.UnaryCellEquivalence
import IntegrationSection3ACVF.PaperBalls

/-! Ordinary unary polydiscs and the sequel's paper-open ball convention.
Within an RV cell the whole-field alternative is excluded explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section5

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}

def unaryInsert (t : Fin m → RV (M := M)) (x : VF (M := M)) : Point (M := M) 1 m :=
  (fun _ => x,t)

def vfShadow (E : Set (Point (M := M) 1 m)) : Set M :=
  {x | ∃ p ∈ E, (vfAt p 0).val = x}

def ordinaryRawOpen (c r : VF (M := M)) : Set M :=
  {x | ∃ hx : iVF x, ¬ iLe (rv (@Sub.sub (VF (M := M)) inferInstance ⟨x,hx⟩ c)).val (rv r).val}

theorem unaryInsert_shadow (E : Set (Point (M := M) 1 m)) (t : Fin m → RV (M := M))
    (hlabel : ∀ p ∈ E, p.2 = t) (x : VF (M := M)) :
    unaryInsert t x ∈ E ↔ x.val ∈ vfShadow E := by
  constructor
  · intro h; exact ⟨unaryInsert t x,h,rfl⟩
  · rintro ⟨p,hp,he⟩
    have hx : unaryInsert t x = p := by
      refine Prod.ext ?_ (hlabel p hp).symm
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact Subtype.ext he.symm
    exact hx.symm ▸ hp

theorem gammaBall_eq_ordinaryRawOpen (c r : VF (M := M)) (γ : Values.Gamma (M := M))
    (hval : Values.vfValueHom r = γ.val) :
    gammaBall c γ true = ordinaryRawOpen c r := by
  ext x
  constructor
  · rintro ⟨hx,hle,hnot⟩
    refine ⟨hx,?_⟩
    rw [← Values.vrv_le_iff]
    change ¬ Values.vfValueHom (@Sub.sub (VF (M := M)) inferInstance ⟨x,hx⟩ c) ≤ Values.vfValueHom r
    rw [hval]
    exact hnot rfl
  · rintro ⟨hx,hnot⟩
    rw [← Values.vrv_le_iff] at hnot
    change ¬ Values.vfValueHom (@Sub.sub (VF (M := M)) inferInstance ⟨x,hx⟩ c) ≤ Values.vfValueHom r at hnot
    rw [hval] at hnot
    exact ⟨hx,(lt_of_not_ge hnot).le,fun _ => hnot⟩

theorem ordinaryRawOpen_paper_open (c r : VF (M := M)) (hr : r ≠ 0) :
    PaperBalls.IsOpenBall (ordinaryRawOpen c r) := by
  have hn : Values.vfValueHom r ≠ Values.infinity := by
    intro h
    exact hr ((CanonicalRV.encodedRv_zero_iff r).mp ((Values.vrv_eq_infinity_iff _).mp h))
  let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom r,hn⟩
  exact Or.inr ⟨c,γ,(gammaBall_eq_ordinaryRawOpen c r γ rfl).symm⟩

theorem paper_open_ordinary {D : Set M} (hD : PaperBalls.IsOpenBall D)
    (hproper : D ≠ {x | iVF x}) :
    ∃ c r : VF (M := M), r ≠ 0 ∧ D = ordinaryRawOpen c r := by
  rcases hD with h | ⟨c,γ,rfl⟩
  · exact (hproper h).elim
  · obtain ⟨t,ht0,htγ⟩ := Values.gamma_has_nonzero_representative γ
    obtain ⟨r,hrt⟩ := CanonicalRV.encodedRv_surjective t
    have hr : r ≠ 0 := by
      intro hz
      exact ht0 ((congrArg Subtype.val hrt).symm.trans ((CanonicalRV.encodedRv_zero_iff r).mpr hz))
    exact ⟨c,r,hr,gammaBall_eq_ordinaryRawOpen c r γ ((congrArg Values.vrv hrt).trans htγ)⟩

theorem vfShadow_polydisc_iff (E : Set (Point (M := M) 1 m)) (t : Fin m → RV (M := M))
    (hlabel : ∀ p ∈ E, p.2 = t) (hproper : vfShadow E ≠ {x | iVF x}) :
    IsUnaryOpenPolydisc E ↔ PaperBalls.IsOpenBall (vfShadow E) := by
  constructor
  · rintro ⟨c,r,hr,s,he⟩
    have hs : vfShadow E = ordinaryRawOpen c r := by
      ext x
      constructor
      · rintro ⟨p,hp,rfl⟩
        rw [he] at hp
        exact ⟨(vfAt p 0).property,hp.1⟩
      · rintro ⟨hx,h⟩
        exact ⟨unaryInsert s ⟨x,hx⟩,he.symm ▸ ⟨h,rfl⟩,rfl⟩
    rw [hs]
    exact ordinaryRawOpen_paper_open c r hr
  · intro h
    obtain ⟨c,r,hr,he⟩ := paper_open_ordinary h hproper
    refine ⟨c,r,hr,t,?_⟩
    ext p
    constructor
    · intro hp
      have hs : (vfAt p 0).val ∈ ordinaryRawOpen c r := he ▸ ⟨p,hp,rfl⟩
      exact ⟨hs.choose_spec,hlabel p hp⟩
    · rintro ⟨hp,ht⟩
      have hs : (vfAt p 0).val ∈ vfShadow E := he.symm ▸ ⟨(vfAt p 0).property,hp⟩
      have hi := (unaryInsert_shadow E t hlabel (vfAt p 0)).mpr hs
      have heq : unaryInsert t (vfAt p 0) = p := by
        refine Prod.ext ?_ ht.symm
        funext i
        exact congrArg p.1 (Subsingleton.elim _ _)
      exact heq ▸ hi

theorem vfShadow_ne_whole_of_cell (E : Set (Point (M := M) 1 m))
    (a : Point (M := M) 1 m) (hcell : ∀ p ∈ E, SameRV p a) :
    vfShadow E ≠ {x | iVF x} := by
  intro he
  have hzero : (0 : VF (M := M)).val ∈ vfShadow E := he.symm ▸ (0 : VF (M := M)).property
  have hone : (1 : VF (M := M)).val ∈ vfShadow E := he.symm ▸ (1 : VF (M := M)).property
  obtain ⟨p,hp,hp0⟩ := hzero
  obtain ⟨q,hq,hq1⟩ := hone
  have hpz : vfAt p 0 = 0 := Subtype.ext hp0
  have hqz := (sameRV_zero_iff ((hcell p hp).trans (hcell q hq).symm)).mp hpz
  exact (one_ne_zero : (1 : VF (M := M)) ≠ 0) ((Subtype.ext hq1).symm.trans hqz)

end IntegrationInACVF.Section5
