import IntegrationSection3ACVF.BallKindGeometry
import IntegrationSection3ACVF.FullBaseDefinability
import IntegrationSection3.CodeEquality

/-! Open/closed-kind tests on actual ball imaginaries, over the original
combined base. The tests take images of all valid codes in the appropriate
charts; no chart representative is selected as a parameter. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.BallKindPredicates

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gammaBall_mem_valuation_closed {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (a r : VFType (M := M)) (γ : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = γ.val) (x : VFType (M := M)) :
    x.val ∈ gammaBall a γ false ↔ v (x-a) ≤ v r := by
  rw [← radiusBall_eq_gammaBall a (CanonicalRV.encodedRv r) γ hr false]
  change (iVF x.val ∧ iLe (iRv r.val) (iRv (iVFAdd x.val (iVFNeg a.val))) ∧
    (false = true → ¬ iLe (iRv (iVFAdd x.val (iVFNeg a.val))) (iRv r.val))) ↔ _
  simp only [Bool.false_eq_true,false_implies,and_true,and_iff_right x.property]
  have hd : (x-a).val = iVFAdd x.val (iVFNeg a.val) := by rw [sub_eq_add_neg]; rfl
  rw [← hd]
  exact hv (x-a) r

theorem paper_closed_code {D : Set M} (hD : PaperBalls.IsClosedBall D) :
    ∃ q : ClosedBallCodes.Code M, ClosedBallCodes.rawBall q.val = D := by
  have hDVF : D ⊆ {x | iVF x} := by
    rcases hD with rfl | ⟨a,rfl⟩ | ⟨a,γ,rfl⟩
    · exact fun _ hx => hx
    · intro x hx
      exact (show x = a.val from hx).symm ▸ a.property
    · exact fun _ hx => hx.choose
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hclosed : ClosedBallRoots.IsClosedBall v {x : VFType (M := M) | x.val ∈ D} := by
    rcases hD with rfl | ⟨a,rfl⟩ | ⟨a,γ,rfl⟩
    · left
      ext x
      exact iff_true_intro x.property
    · right
      refine ⟨a,0,?_⟩
      rw [map_zero,ValOneEC.closedBall_zero_radius]
      ext x
      exact ⟨Subtype.ext,congrArg Subtype.val⟩
    · obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
      exact Or.inr ⟨a,r,Set.ext (gammaBall_mem_valuation_closed v hv a r γ hr)⟩
  obtain ⟨t,ht,he⟩ := ClosedBallCodes.exists_code_of_closed v hv _ hclosed
  refine ⟨⟨t,ht⟩,Set.ext fun x => ?_⟩
  constructor
  · intro hx
    exact (Set.ext_iff.mp he (⟨x,hx.2.1⟩ : VFType (M := M))).mpr hx
  · intro hx
    exact (Set.ext_iff.mp he (⟨x,hDVF hx⟩ : VFType (M := M))).mp hx

def openCodes : Set (Fin 4 → M) :=
  {c | c ∈ BallPresentation.codeDomain ∧ (c 3 ≠ iVFZero ∨ c 2 = iVFZero)}

def closedCodes : Set (Fin 4 → M) :=
  {c | c ∈ BallPresentation.codeDomain ∧ c 3 = iVFZero}

theorem chartCodes_definable (Q : Set M) :
    @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin 4) openCodes ∧
      @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin 4) closedCodes := by
  let O := openCodes (M := M)
  let C := closedCodes (M := M)
  let D := BallPresentation.codeDomain (M := M)
  let z0 := @iVFZero M sM
  have hd := BallPresentation.codeDomain_definable (M := M) Q
  let N := @CanonicalStructure.normalize M sM
  have hz : @iVFZero M N = z0 := @CanonicalStructure.sortZero_normalize M sM .vf
  have hzero : @Set.DefinableFun M LRV N (Fin 4) Q (fun _ => z0) := by
    rw [← hz]
    letI := N
    exact SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  letI := N
  have h3 := (@Set.DefinableFun.proj M LRV N (Fin 4) Q 3).ofPred_eq hzero
  have h2 := (@Set.DefinableFun.proj M LRV N (Fin 4) Q 2).ofPred_eq hzero
  change Q.Definable LRV O ∧ Q.Definable LRV C
  exact ⟨hd.inter (h3.compl.union h2),hd.inter h3⟩

theorem open_image_eq : CodeEquality.imageCodes
    (@BallPresentation.presentation M sM hM) openCodes =
      {i | PaperBalls.IsOpenBall (BallImaginaries.underlying i)} := by
  ext i
  change i ∈ CodeEquality.imageCodes (@BallPresentation.presentation M sM hM) openCodes ↔
    PaperBalls.IsOpenBall (BallImaginaries.underlying i)
  constructor
  · rintro ⟨c,hc,hvalid,hdecode⟩
    have he := BallPresentation.underlying_decode (⟨c,hvalid⟩ : BallPresentation.codeDomain)
    change BallPresentation.decode ⟨c,hvalid⟩ = i at hdecode
    rw [hdecode] at he
    by_cases h3 : c 3 = iVFZero
    · have h2 : c 2 = iVFZero := hc.2.resolve_left (fun hn => hn h3)
      left
      rw [he,if_pos h3]
      have hs : ∀ j, iVF (BallPresentation.closedTuple c j) :=
        (hvalid.resolve_right (fun hn => hn.1 h3)).2
      ext x
      simp only [ClosedBallCodes.rawBall,Set.mem_ofPred_eq,ClosedBallCodes.body_realize,
        and_iff_right hs]
      change (iVF x ∧ (c 2 = iVFZero ∨ _)) ↔ iVF x
      simp only [h2,true_or,and_true]
    · rw [he,if_neg h3]
      exact BallKindGeometry.open_raw_isOpenBall
        ⟨BallPresentation.openTuple c,(hvalid.resolve_left (fun hz => h3 hz.1)).2⟩
  · intro hi
    rcases hi with hVF | ⟨a,γ,hordinary⟩
    · let q : ClosedBallCodes.Code M := ⟨![iVFZero,iVFZero,iVFZero],by
        intro j
        fin_cases j <;> exact (0 : VFType (M := M)).property⟩
      let d := BallPresentation.encodeClosed q
      refine ⟨d.val,⟨d.property,Or.inr rfl⟩,d.property,?_⟩
      change BallPresentation.decode (BallPresentation.encodeClosed q) = i
      apply BallImaginaries.underlying_injective
      rw [BallPresentation.decode_encodeClosed]
      change ClosedBallCodes.rawBall q.val = BallImaginaries.underlying i
      rw [hVF]
      ext x
      simp only [ClosedBallCodes.rawBall,Set.mem_ofPred_eq,ClosedBallCodes.body_realize,
        and_iff_right q.property]
      change (iVF x ∧ (iVFZero = iVFZero ∨ _)) ↔ iVF x
      simp only [true_or,and_true]
    · obtain ⟨q,hq⟩ := BallKindGeometry.gammaBall_open_code a γ
      let d := BallPresentation.encodeOpen q
      have h3 : d.val 3 ≠ iVFZero := by
        intro he
        exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he)
      refine ⟨d.val,⟨d.property,Or.inl h3⟩,d.property,?_⟩
      change BallPresentation.decode (BallPresentation.encodeOpen q) = i
      apply BallImaginaries.underlying_injective
      rw [BallPresentation.decode_encodeOpen]
      exact hq.trans hordinary.symm

theorem closed_image_eq : CodeEquality.imageCodes
    (@BallPresentation.presentation M sM hM) closedCodes =
      {i | PaperBalls.IsClosedBall (BallImaginaries.underlying i)} := by
  ext i
  change i ∈ CodeEquality.imageCodes (@BallPresentation.presentation M sM hM) closedCodes ↔
    PaperBalls.IsClosedBall (BallImaginaries.underlying i)
  constructor
  · rintro ⟨c,hc,hvalid,hdecode⟩
    have he := BallPresentation.underlying_decode (⟨c,hvalid⟩ : BallPresentation.codeDomain)
    change BallPresentation.decode ⟨c,hvalid⟩ = i at hdecode
    rw [hdecode,if_pos hc.2] at he
    rw [he]
    exact BallKindGeometry.closed_raw_isClosedBall
      ⟨BallPresentation.closedTuple c,(hvalid.resolve_right (fun hn => hn.1 hc.2)).2⟩
  · intro hi
    obtain ⟨q,hq⟩ := paper_closed_code hi
    let d := BallPresentation.encodeClosed q
    refine ⟨d.val,⟨d.property,rfl⟩,d.property,?_⟩
    change BallPresentation.decode (BallPresentation.encodeClosed q) = i
    apply BallImaginaries.underlying_injective
    rw [BallPresentation.decode_encodeClosed]
    exact hq

theorem open_family_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.Family B {i | PaperBalls.IsOpenBall (BallImaginaries.underlying i)} := by
  let U := BallImaginaries.underlying (M := M)
  let O := openCodes (M := M)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have he := open_image_eq (M := M)
  have hinj := BallImaginaries.underlying_injective (M := M)
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have ho := (chartCodes_definable (M := M) B.real).1
  have hd : FullBaseAtomicity.Family B (CodeEquality.imageCodes q O) := by
    letI := CanonicalStructure.normalize (M := M)
    exact CodeEquality.imageCodes_definable hp hq
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hinj
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) ho)
  change FullBaseAtomicity.Family B
    (CodeEquality.imageCodes (@BallPresentation.presentation M sM hM) openCodes) at hd
  rw [he] at hd
  exact hd

theorem closed_family_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.Family B {i | PaperBalls.IsClosedBall (BallImaginaries.underlying i)} := by
  let U := BallImaginaries.underlying (M := M)
  let C := closedCodes (M := M)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have he := closed_image_eq (M := M)
  have hinj := BallImaginaries.underlying_injective (M := M)
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hc := (chartCodes_definable (M := M) B.real).2
  have hd : FullBaseAtomicity.Family B (CodeEquality.imageCodes q C) := by
    letI := CanonicalStructure.normalize (M := M)
    exact CodeEquality.imageCodes_definable hp hq
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hinj
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hc)
  change FullBaseAtomicity.Family B
    (CodeEquality.imageCodes (@BallPresentation.presentation M sM hM) closedCodes) at hd
  rw [he] at hd
  exact hd

end IntegrationInACVF.Section3ACVF.BallKindPredicates
