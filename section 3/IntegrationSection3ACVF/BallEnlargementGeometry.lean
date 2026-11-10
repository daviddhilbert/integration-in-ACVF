import IntegrationSection3ACVF.PaperBallInvariants
import IntegrationSection3ACVF.FullGammaRadius
import IntegrationSection3.ValuationEnlargement

/-! Actual-ball geometry for nonmaximal-hole enlargement.
The valuation lemmas it uses have passed the generic core audit. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity

namespace IntegrationInACVF.Section3ACVF.BallEnlargementGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem valuation_le_of_gamma_le {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {α β : Values.Gamma (M := M)} (r s : VFType (M := M))
    (hr : Values.vfValueHom r = α.val) (hs : Values.vfValueHom s = β.val)
    (hαβ : α ≤ β) : v s ≤ v r := by
  apply (hv s r).mp
  apply (Values.vf_pred_iff_gamma_le s r).mpr
  rw [hr,hs]
  exact hαβ

theorem valuation_lt_of_gamma_lt {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {α β : Values.Gamma (M := M)} (r s : VFType (M := M))
    (hr : Values.vfValueHom r = α.val) (hs : Values.vfValueHom s = β.val)
    (hαβ : α < β) : v s < v r := by
  apply lt_of_not_ge
  intro hn
  have hp := (Values.vf_pred_iff_gamma_le r s).mp ((hv r s).mpr hn)
  rw [hr,hs] at hp
  exact not_le_of_gt hαβ hp

theorem ordinary_presentation {D : Set M} (α : Values.Gamma (M := M))
    (hr : PaperBalls.HasRadius D (↑α.val : PaperBalls.Radius (M := M))) :
    ∃ a : VFType (M := M), ∃ strict : Bool, D = gammaBall a α strict := by
  rcases hr with ⟨_,he⟩ | ⟨a,_,he⟩ | ⟨a,β,strict,hD,he⟩
  · exact (WithBot.coe_ne_bot he).elim
  · exact (α.property (WithBot.coe_inj.mp he)).elim
  · have hαβ : α = β := Subtype.ext (WithBot.coe_inj.mp he)
    refine ⟨a,strict,?_⟩
    rw [hαβ]
    exact hD

theorem gammaBall_centre_mem (a : VFType (M := M)) (α : Values.Gamma (M := M)) (strict : Bool) :
    a.val ∈ gammaBall a α strict := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  cases strict with
  | false =>
    apply (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr a).mpr
    simpa only [sub_self,map_zero] using (zero_le : (0 : Γ) ≤ v r)
  | true =>
    have hr0 : r ≠ 0 := by
      intro hz
      have h_inf : Values.vfValueHom r = Values.infinity := by
        rw [hz,map_zero]
        exact Values.infinity_eq_zero.symm
      exact α.property (hr.symm.trans h_inf)
    apply (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr a).mpr
    simpa only [sub_self,map_zero] using (zero_lt_iff.mpr ((v.ne_zero_iff).mpr hr0))

theorem gammaBall_isBall (a : VFType (M := M)) (α : Values.Gamma (M := M)) (strict : Bool) :
    IsBall (gammaBall a α strict) := by
  cases strict with
  | false =>
    obtain ⟨q,hq⟩ := BallKindGeometry.gammaBall_closed_code a α
    rw [← hq]
    exact BallCodeGeometry.closed_raw_isBall q
  | true =>
    obtain ⟨q,hq⟩ := BallKindGeometry.gammaBall_open_code a α
    rw [← hq]
    exact BallCodeGeometry.open_raw_isBall q

theorem closed_ball_coded (a : VFType (M := M)) (α : Values.Gamma (M := M)) :
    ∃ k : BallImaginaries.Ball M, BallImaginaries.underlying k = gammaBall a α false ∧
      PaperBalls.IsClosedBall (BallImaginaries.underlying k) ∧
      PaperBalls.HasRadius (BallImaginaries.underlying k) (↑α.val : PaperBalls.Radius (M := M)) := by
  obtain ⟨k,hk⟩ := BallCodeGeometry.encodedBall_coded (gammaBall a α false) (gammaBall_isBall a α false)
  exact ⟨k,hk,Or.inr (Or.inr ⟨a,α,hk⟩),Or.inr (Or.inr ⟨a,α,false,hk,rfl⟩)⟩

theorem vf_ssubset_lift {P Q : Set M} (hP : P ⊆ {x | iVF x})
    (hsub : {x : VFType (M := M) | x.val ∈ P} ⊂ {x | x.val ∈ Q}) : P ⊂ Q := by
  refine ⟨fun x hx => hsub.1 (show (⟨x,hP hx⟩ : VFType (M := M)).val ∈ P from hx),?_⟩
  intro hrev
  exact hsub.2 (fun x hx => hrev hx)

theorem vf_eq_lift {P Q : Set M} (hP : P ⊆ {x | iVF x}) (hQ : Q ⊆ {x | iVF x})
    (he : {x : VFType (M := M) | x.val ∈ P} = {x | x.val ∈ Q}) : P = Q := by
  ext x
  constructor
  · intro hx
    exact (Set.ext_iff.mp he (⟨x,hP hx⟩ : VFType (M := M))).mp hx
  · intro hx
    exact (Set.ext_iff.mp he (⟨x,hQ hx⟩ : VFType (M := M))).mpr hx

theorem gamma_same_kind_eq_of_subset (a b : VFType (M := M))
    (α : Values.Gamma (M := M)) (strict : Bool)
    (hsub : gammaBall a α strict ⊆ gammaBall b α strict) :
    gammaBall a α strict = gammaBall b α strict := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  have ha := hsub (gammaBall_centre_mem a α strict)
  have htrans (x y z : VFType (M := M)) :
      v (x-z) ≤ max (v (x-y)) (v (y-z)) := by
    have he : x-z = (x-y)+(y-z) := by ring
    rw [he]
    exact v.map_add _ _
  apply vf_eq_lift (fun _ hx => hx.choose) (fun _ hx => hx.choose)
  cases strict with
  | false =>
    have hav := (BallKindPredicates.gammaBall_mem_valuation_closed v hv b r α hr a).mp ha
    have hba : v (b-a) ≤ v r := by rwa [v.map_sub_swap]
    have he : {x : VFType (M := M) | v (x-a) ≤ v r} = {x | v (x-b) ≤ v r} := by
      ext x
      exact ⟨fun hx => (htrans x a b).trans (max_le hx hav),
        fun hx => (htrans x b a).trans (max_le hx hba)⟩
    ext x
    exact (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr x).trans
      ((Set.ext_iff.mp he x).trans (BallKindPredicates.gammaBall_mem_valuation_closed v hv b r α hr x).symm)
  | true =>
    have hav := (GammaCosetGeometry.gammaBall_mem_valuation v hv b r α hr a).mp ha
    have hba : v (b-a) < v r := by rwa [v.map_sub_swap]
    have he : {x : VFType (M := M) | v (x-a) < v r} = {x | v (x-b) < v r} := by
      ext x
      exact ⟨fun hx => (htrans x a b).trans_lt (max_lt hx hav),
        fun hx => (htrans x b a).trans_lt (max_lt hx hba)⟩
    ext x
    exact (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr x).trans
      ((Set.ext_iff.mp he x).trans (GammaCosetGeometry.gammaBall_mem_valuation v hv b r α hr x).symm)

theorem closed_not_subset_open_same_radius (a b : VFType (M := M))
    (α : Values.Gamma (M := M)) : ¬ gammaBall a α false ⊆ gammaBall b α true := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  intro hsub
  have hs : {x : VFType (M := M) | v (x-a) ≤ v r} ⊆ {x | v (x-b) < v r} := by
    intro x hx
    exact (GammaCosetGeometry.gammaBall_mem_valuation v hv b r α hr x).mp
      (hsub ((BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr x).mpr hx))
  exact lt_irrefl _ (ValuationRadius.closed_radius_lt_of_subset_open v a b r r hs)

theorem proper_same_radius_kinds (a b : VFType (M := M))
    (α : Values.Gamma (M := M)) (holeStrict parentStrict : Bool)
    (hproper : gammaBall a α holeStrict ⊂ gammaBall b α parentStrict) :
    holeStrict = true ∧ parentStrict = false := by
  cases holeStrict <;> cases parentStrict
  · have he := gamma_same_kind_eq_of_subset a b α false hproper.1
    exact (hproper.2 he.symm.subset).elim
  · exact (closed_not_subset_open_same_radius a b α hproper.1).elim
  · exact ⟨rfl,rfl⟩
  · have he := gamma_same_kind_eq_of_subset a b α true hproper.1
    exact (hproper.2 he.symm.subset).elim

theorem gamma_radius_le_of_subset (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a b : VFType (M := M)) (α β : Values.Gamma (M := M)) (holeStrict parentStrict : Bool)
    (hsub : gammaBall a β holeStrict ⊆ gammaBall b α parentStrict) : α ≤ β := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  obtain ⟨s,hs⟩ := GammaCosetGeometry.vf_representative β
  have hs0 : s ≠ 0 := by
    intro hz
    have h_inf : Values.vfValueHom s = Values.infinity := by
      rw [hz,map_zero]
      exact Values.infinity_eq_zero.symm
    exact β.property (hs.symm.trans h_inf)
  have hle : v s ≤ v r := by
    cases holeStrict with
    | false =>
      cases parentStrict with
      | false =>
        apply ValuationRadius.closed_radius_le_of_subset v a b s r
        intro x hx
        exact (BallKindPredicates.gammaBall_mem_valuation_closed v hv b r α hr x).mp
          (hsub ((BallKindPredicates.gammaBall_mem_valuation_closed v hv a s β hs x).mpr hx))
      | true =>
        apply (ValuationRadius.closed_radius_lt_of_subset_open v a b s r ?_).le
        intro x hx
        exact (GammaCosetGeometry.gammaBall_mem_valuation v hv b r α hr x).mp
          (hsub ((BallKindPredicates.gammaBall_mem_valuation_closed v hv a s β hs x).mpr hx))
    | true =>
      cases parentStrict with
      | false =>
        apply ValuationRadius.open_radius_le_of_subset_closed v
          (BallRadiusGeometry.valuation_dense v hv δ hδ) a b s r hs0
        intro x hx
        exact (BallKindPredicates.gammaBall_mem_valuation_closed v hv b r α hr x).mp
          (hsub ((GammaCosetGeometry.gammaBall_mem_valuation v hv a s β hs x).mpr hx))
      | true =>
        apply Balls.strictDisc_radius_le_of_subset v a b s r hs0
        intro x hx
        exact (GammaCosetGeometry.gammaBall_mem_valuation v hv b r α hr x).mp
          (hsub ((GammaCosetGeometry.gammaBall_mem_valuation v hv a s β hs x).mpr hx))
  have hp := (Values.vf_pred_iff_gamma_le s r).mp ((hv s r).mpr hle)
  rw [hr,hs] at hp
  exact hp

theorem open_inside_closed_same_radius (a b : VFType (M := M))
    (α : Values.Gamma (M := M)) (ha : a.val ∈ gammaBall b α false) :
    gammaBall a α true ⊂ gammaBall b α false := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  have hav := (BallKindPredicates.gammaBall_mem_valuation_closed v hv b r α hr a).mp ha
  refine ⟨?_,?_⟩
  · intro x hx
    let u : VFType (M := M) := ⟨x,hx.choose⟩
    have huv := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr u).mp hx
    apply (BallKindPredicates.gammaBall_mem_valuation_closed v hv b r α hr u).mpr
    have he : u-b = (u-a)+(a-b) := by ring
    rw [he]
    exact (v.map_add _ _).trans (max_le huv.le hav)
  · intro hrev
    exact closed_not_subset_open_same_radius b a α hrev

theorem gammaBall_strict_enlargement (a : VFType (M := M))
    (α β : Values.Gamma (M := M)) (hαβ : α < β) (strict : Bool) :
    gammaBall a β strict ⊂ gammaBall a α false := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative β
  obtain ⟨t,ht⟩ := GammaCosetGeometry.vf_representative α
  have hrt := valuation_lt_of_gamma_lt v hv t r ht hr hαβ
  have hbound : {x : VFType (M := M) | x.val ∈ gammaBall a β strict} ⊆
      {x | v (x-a) ≤ v r} := by
    intro x hx
    cases strict with
    | false => exact (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r β hr x).mp hx
    | true => exact ((GammaCosetGeometry.gammaBall_mem_valuation v hv a r β hr x).mp hx).le
  have hs := ValuationEnlargement.strict_enlargement v a r t hbound hrt
  have he : {x : VFType (M := M) | x.val ∈ gammaBall a α false} =
      {x | v (x-a) ≤ v t} := Set.ext (fun x =>
        BallKindPredicates.gammaBall_mem_valuation_closed v hv a t α ht x)
  rw [← he] at hs
  exact vf_ssubset_lift (fun _ hx => hx.choose) hs

theorem closed_inside_parent (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a b : VFType (M := M)) (α ρ : Values.Gamma (M := M)) (hαρ : α < ρ)
    (strict : Bool) (ha : a.val ∈ gammaBall b α strict) :
    gammaBall a ρ false ⊂ gammaBall b α strict := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨t,ht⟩ := GammaCosetGeometry.vf_representative ρ
  obtain ⟨s,hs⟩ := GammaCosetGeometry.vf_representative α
  have hts := valuation_lt_of_gamma_lt v hv s t hs ht hαρ
  have he : {x : VFType (M := M) | x.val ∈ gammaBall a ρ false} =
      {x | v (x-a) ≤ v t} := Set.ext (fun x =>
        BallKindPredicates.gammaBall_mem_valuation_closed v hv a t ρ ht x)
  apply vf_ssubset_lift (fun _ hx => hx.choose)
  rw [he]
  cases strict with
  | false =>
    have hb := (BallKindPredicates.gammaBall_mem_valuation_closed v hv b s α hs a).mp ha
    have hh := ValuationEnlargement.closed_ssubset_closed v a b t s hb hts
    have hp : {x : VFType (M := M) | x.val ∈ gammaBall b α false} =
        {x | v (x-b) ≤ v s} := Set.ext (fun x =>
          BallKindPredicates.gammaBall_mem_valuation_closed v hv b s α hs x)
    rwa [hp]
  | true =>
    have hb := (GammaCosetGeometry.gammaBall_mem_valuation v hv b s α hs a).mp ha
    have hh := ValuationEnlargement.closed_ssubset_open v
      (BallRadiusGeometry.valuation_dense v hv δ hδ) a b t s hb hts
    have hp : {x : VFType (M := M) | x.val ∈ gammaBall b α true} =
        {x | v (x-b) < v s} := Set.ext (fun x =>
          GammaCosetGeometry.gammaBall_mem_valuation v hv b s α hs x)
    rwa [hp]

theorem gammaBall_proper_in_vf (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (strict : Bool) :
    gammaBall a α strict ⊂ {x | iVF x} := by
  have hsub : gammaBall a α strict ⊆ {x | iVF x} := fun _ hx => hx.choose
  refine ⟨hsub,fun hrev => ?_⟩
  exact BallRadiusGeometry.gammaBall_ne_vf δ hδ a α strict (Set.Subset.antisymm hsub hrev)

theorem singleton_strict_enlargement (a : VFType (M := M)) (α : Values.Gamma (M := M)) :
    {a.val} ⊂ gammaBall a α false := by
  have ha : a.val ∈ gammaBall a α false := by
    obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
    apply (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr a).mpr
    simpa only [sub_self,map_zero] using (zero_le : (0 : Γ) ≤ v r)
  have hsub : {a.val} ⊆ gammaBall a α false := by
    intro x hx
    have he : x = a.val := hx
    exact he.symm ▸ ha
  refine ⟨hsub,fun hrev => ?_⟩
  exact BallRadiusGeometry.gamma_closed_ne_singleton a a α (Set.Subset.antisymm hrev hsub)

theorem closed_fixed_radius_unique (B : FullBaseAtomicity.Base (M := M))
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α})
    (a b : VFType (M := M))
    (hne : (gammaBall a α false ∩ gammaBall b α false).Nonempty) :
    gammaBall a α false = gammaBall b α false := by
  obtain ⟨H,_,hH⟩ := FullGammaRadius.gamma_subgroup B α hα false
  obtain ⟨x,hxa,hxb⟩ := hne
  let u : VFType (M := M) := ⟨x,hxa.choose⟩
  have hua : QuotientAddGroup.mk' H u = QuotientAddGroup.mk' H a := by
    apply (GammaCosetGeometry.cosetBody_mem H u a).mp
    rwa [hH a]
  have hub : QuotientAddGroup.mk' H u = QuotientAddGroup.mk' H b := by
    apply (GammaCosetGeometry.cosetBody_mem H u b).mp
    rwa [hH b]
  have hab := hua.symm.trans hub
  rw [← hH a,← hH b]
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,hz.trans hab,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,hz.trans hab.symm,rfl⟩

theorem closed_ordinary_presentation (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {D : Set M} (hD : PaperBalls.IsClosedBall D) (α : Values.Gamma (M := M))
    (hr : PaperBalls.HasRadius D (↑α.val : PaperBalls.Radius (M := M))) :
    ∃ a : VFType (M := M), D = gammaBall a α false := by
  rcases hD with hVF | ⟨a,ha⟩ | ⟨a,β,ha⟩
  · have he := PaperBallInvariants.hasRadius_unique δ hδ hr (Or.inl ⟨hVF,rfl⟩)
    exact (WithBot.coe_ne_bot he).elim
  · have he := PaperBallInvariants.hasRadius_unique δ hδ hr (Or.inr (Or.inl ⟨a,ha,rfl⟩))
    exact (α.property (WithBot.coe_inj.mp he)).elim
  · have he := PaperBallInvariants.hasRadius_unique δ hδ hr (Or.inr (Or.inr ⟨a,β,false,ha,rfl⟩))
    have hαβ : α = β := Subtype.ext (WithBot.coe_inj.mp he)
    refine ⟨a,?_⟩
    rw [hαβ]
    exact ha

theorem closed_supersets_unique (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α})
    (D : Set M) (hne : D.Nonempty) (k l : BallImaginaries.Ball M)
    (hkClosed : PaperBalls.IsClosedBall (BallImaginaries.underlying k))
    (hkRadius : PaperBalls.HasRadius (BallImaginaries.underlying k) (↑α.val : PaperBalls.Radius (M := M)))
    (hlClosed : PaperBalls.IsClosedBall (BallImaginaries.underlying l))
    (hlRadius : PaperBalls.HasRadius (BallImaginaries.underlying l) (↑α.val : PaperBalls.Radius (M := M)))
    (hk : D ⊆ BallImaginaries.underlying k) (hl : D ⊆ BallImaginaries.underlying l) : k = l := by
  obtain ⟨a,ha⟩ := closed_ordinary_presentation δ hδ hkClosed α hkRadius
  obtain ⟨b,hb⟩ := closed_ordinary_presentation δ hδ hlClosed α hlRadius
  apply BallImaginaries.underlying_injective
  rw [ha,hb]
  apply closed_fixed_radius_unique B α hα a b
  obtain ⟨x,hx⟩ := hne
  refine ⟨x,?_,?_⟩
  · rw [← ha]
    exact hk hx
  · rw [← hb]
    exact hl hx

theorem fixed_radius_enlargements_finite (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α})
    (I : Set (BallImaginaries.Ball M)) (hI : I.Finite) (P : Set M) :
    {k : BallImaginaries.Ball M | ∃ h ∈ I,
      PaperBalls.IsClosedBall (BallImaginaries.underlying k) ∧
      PaperBalls.HasRadius (BallImaginaries.underlying k) (↑α.val : PaperBalls.Radius (M := M)) ∧
      BallImaginaries.underlying h ⊆ BallImaginaries.underlying k ∧
      BallImaginaries.underlying k ⊂ P}.Finite := by
  let U := BallImaginaries.underlying (M := M)
  let C := fun h : BallImaginaries.Ball M => {k : BallImaginaries.Ball M |
    PaperBalls.IsClosedBall (U k) ∧ PaperBalls.HasRadius (U k) (↑α.val : PaperBalls.Radius (M := M)) ∧
      U h ⊆ U k ∧ U k ⊂ P}
  have hC (h : BallImaginaries.Ball M) : (C h).Subsingleton := by
    intro k hk l hl
    exact closed_supersets_unique B δ hδ α hα (U h)
      (CanonicalBallSupport.encodedBall_nonempty (BallCodeGeometry.underlying_isBall h)) k l
      hk.1 hk.2.1 hl.1 hl.2.1 hk.2.2.1 hl.2.2.1
  have hf := hI.biUnion (fun h _ => (hC h).finite)
  convert hf using 1
  ext k
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq,exists_prop,C,U]

end IntegrationInACVF.Section3ACVF.BallEnlargementGeometry
