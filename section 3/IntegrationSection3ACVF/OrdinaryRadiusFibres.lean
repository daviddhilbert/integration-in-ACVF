import IntegrationSection3ACVF.OrdinaryCentreFibres

/-! Intrinsic ordinary-radius fibres, using every real chart code of an
actual ball. Special whole-field and singleton charts are excluded from
the ordinary graph by their flags and the nonzero field-value guard. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.OrdinaryRadiusFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def ordinaryRadiusFibre (D : Set M) : Set M :=
  {t | ∃ ht : iRV t, t ≠ iRVZero ∧
    PaperBalls.HasRadius D (↑(Values.vrv ⟨t,ht⟩) : PaperBalls.Radius (M := M))}

def RadiusCodes : Set (Fin 4 ⊕ Fin 1 → M) :=
  {z | z ∘ Sum.inl ∈ BallPresentation.codeDomain ∧
    (z (.inl 3) ≠ iVFZero ∨ z (.inl 2) ≠ iVFZero) ∧
    OrdinaryCentreFibres.fieldValueEq ![z (.inl 1),z (.inr 0)]}

theorem radiusCodes_definable (Q : Set M) :
    @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin 4 ⊕ Fin 1) RadiusCodes := by
  let R := RadiusCodes (M := M)
  let z0 := @iVFZero M sM
  have hd := BallPresentation.codeDomain_definable (M := M) Q
  have hv := OrdinaryCentreFibres.fieldValueEq_definable (M := M) Q
  let N := @CanonicalStructure.normalize M sM
  have hz : @iVFZero M N = z0 := @CanonicalStructure.sortZero_normalize M sM .vf
  have hzero : @Set.DefinableFun M LRV N (Fin 4 ⊕ Fin 1) Q (fun _ => z0) := by
    rw [← hz]
    letI := N
    exact SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  letI := N
  have h3 := (@Set.DefinableFun.proj M LRV N (Fin 4 ⊕ Fin 1) Q (.inl 3)).ofPred_eq hzero
  have h2 := (@Set.DefinableFun.proj M LRV N (Fin 4 ⊕ Fin 1) Q (.inl 2)).ofPred_eq hzero
  have hD := hd.preimage_comp (Sum.inl : Fin 4 → Fin 4 ⊕ Fin 1)
  have hV := hv.preimage_comp (![.inl 1,.inr 0] : Fin 2 → Fin 4 ⊕ Fin 1)
  change Q.Definable LRV R
  exact hD.inter ((h3.compl.union h2.compl).inter hV)

theorem code_has_radius (c : BallPresentation.codeDomain (M := M))
    (t : CanonicalRV.RVSort M) (ht0 : t.val ≠ iRVZero)
    (hc : Sum.elim c.val ![t.val] ∈ RadiusCodes) :
    PaperBalls.HasRadius (BallImaginaries.underlying (BallPresentation.decode c))
      (↑(Values.vrv t) : PaperBalls.Radius (M := M)) := by
  let γ := Values.gammaOf t ht0
  have he := BallPresentation.underlying_decode c
  have hconds : c.val 3 ≠ iVFZero ∨ c.val 2 ≠ iVFZero := hc.2.1
  have hvalue : OrdinaryCentreFibres.fieldValueEq ![c.val 1,t.val] := hc.2.2
  by_cases h3 : c.val 3 = iVFZero
  · have hs : ∀ j, iVF (BallPresentation.closedTuple c.val j) :=
      (c.property.resolve_right (fun hn => hn.1 h3)).2
    let q : ClosedBallCodes.Code M := ⟨BallPresentation.closedTuple c.val,hs⟩
    let a : VFType (M := M) := ⟨c.val 0,hs 0⟩
    let r : VFType (M := M) := ⟨c.val 1,hs 1⟩
    have hr : Values.vfValueHom r = γ.val :=
      (OrdinaryCentreFibres.fieldValueEq_iff r t ht0).mp hvalue
    have hflag : q.val 2 ≠ iVFZero := hconds.resolve_left (fun hn => hn h3)
    refine Or.inr (Or.inr ⟨a,γ,false,?_,rfl⟩)
    rw [he,if_pos h3]
    exact BallKindGeometry.closed_raw_gammaBall q hflag γ hr
  · have hs : OpenBallCodes.Proper (BallPresentation.openTuple c.val) :=
      (c.property.resolve_left (fun hz => h3 hz.1)).2
    let q : OpenBallCodes.Code M := ⟨BallPresentation.openTuple c.val,hs⟩
    let a : VFType (M := M) := ⟨c.val 0,hs.1 0⟩
    let r : VFType (M := M) := ⟨c.val 1,hs.1 1⟩
    have hr : Values.vfValueHom r = γ.val :=
      (OrdinaryCentreFibres.fieldValueEq_iff r t ht0).mp hvalue
    refine Or.inr (Or.inr ⟨a,γ,true,?_,rfl⟩)
    rw [he,if_neg h3]
    exact BallKindGeometry.open_raw_gammaBall q γ hr

theorem hasRadius_code (i : BallImaginaries.Ball M) (t : CanonicalRV.RVSort M)
    (ht0 : t.val ≠ iRVZero)
    (hr : PaperBalls.HasRadius (BallImaginaries.underlying i)
      (↑(Values.vrv t) : PaperBalls.Radius (M := M))) :
    ∃ c : BallPresentation.codeDomain (M := M),
      Sum.elim c.val ![t.val] ∈ RadiusCodes ∧ BallPresentation.decode c = i := by
  rcases hr with ⟨_,he⟩ | ⟨_,_,he⟩ | ⟨a,γ,strict,hbody,he⟩
  · exact (WithBot.coe_ne_bot he).elim
  · exact (ht0 ((Values.vrv_eq_infinity_iff t).mp (WithBot.coe_inj.mp he))).elim
  · obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
    have hrv : Values.vfValueHom r = Values.vrv t := hr.trans (WithBot.coe_inj.mp he).symm
    have hvalue := (OrdinaryCentreFibres.fieldValueEq_iff r t ht0).mpr hrv
    have hr0 : r.val ≠ iVFZero := by
      intro hz
      have hrz : r = 0 := Subtype.ext hz
      have h_inf : Values.vfValueHom r = Values.infinity := by
        rw [hrz,map_zero]; exact Values.infinity_eq_zero.symm
      exact γ.property (hr.symm.trans h_inf)
    have hflag : iVFOne (M := M) ≠ iVFZero := by
      intro hz
      exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext hz)
    cases strict with
    | false =>
      let q : ClosedBallCodes.Code M := ⟨![a.val,r.val,iVFOne],by
        intro j
        fin_cases j
        · exact a.property
        · exact r.property
        · exact (1 : VFType (M := M)).property⟩
      let c := BallPresentation.encodeClosed q
      refine ⟨c,?_,?_⟩
      · exact ⟨c.property,Or.inr hflag,hvalue⟩
      · change BallPresentation.decode (BallPresentation.encodeClosed q) = i
        apply BallImaginaries.underlying_injective
        rw [BallPresentation.decode_encodeClosed]
        change ClosedBallCodes.rawBall q.val = BallImaginaries.underlying i
        exact (BallKindGeometry.closed_raw_gammaBall q hflag γ hr).trans hbody.symm
    | true =>
      let q : OpenBallCodes.Code M := ⟨![a.val,r.val],by
        refine ⟨?_,hr0⟩
        intro j
        fin_cases j
        · exact a.property
        · exact r.property⟩
      let c := BallPresentation.encodeOpen q
      refine ⟨c,?_,?_⟩
      · exact ⟨c.property,Or.inl hflag,hvalue⟩
      · change BallPresentation.decode (BallPresentation.encodeOpen q) = i
        apply BallImaginaries.underlying_injective
        rw [BallPresentation.decode_encodeOpen]
        change OpenBallCodes.rawBall q.val = BallImaginaries.underlying i
        exact (BallKindGeometry.open_raw_gammaBall q γ hr).trans hbody.symm

theorem image_eq : CodeEquality.imageCodeRelation (@BallPresentation.presentation M sM hM) RadiusCodes =
    fun i => ordinaryRadiusFibre (BallImaginaries.underlying i) := by
  funext i
  ext t
  constructor
  · rintro ⟨c,hc,he⟩
    have hvalue : OrdinaryCentreFibres.fieldValueEq ![c.val 1,t] := hc.2.2
    have ht : GammaParameters.NonzeroRV t := hvalue.2.2.1
    refine ⟨ht.1,ht.2,?_⟩
    have hr := code_has_radius c ⟨t,ht.1⟩ ht.2 hc
    change BallPresentation.decode c = i at he
    rwa [he] at hr
  · rintro ⟨ht,h0,hr⟩
    obtain ⟨c,hc,he⟩ := hasRadius_code i ⟨t,ht⟩ h0 hr
    exact ⟨c,hc,he⟩

theorem relation_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.Relation B (fun i => ordinaryRadiusFibre (BallImaginaries.underlying i)) := by
  let U := BallImaginaries.underlying (M := M)
  let R := RadiusCodes (M := M)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have he := image_eq (M := M)
  have hinj := BallImaginaries.underlying_injective (M := M)
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hR := radiusCodes_definable (M := M) B.real
  have hd : FullBaseAtomicity.Relation B (CodeEquality.imageCodeRelation q R) := by
    letI := CanonicalStructure.normalize (M := M)
    exact CodeEquality.imageCodeRelation_definable hp hq
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hinj
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hR)
  change FullBaseAtomicity.Relation B
    (CodeEquality.imageCodeRelation (@BallPresentation.presentation M sM hM) RadiusCodes) at hd
  rw [he] at hd
  exact hd

theorem mem_ordinaryRadiusFibre_iff (D : Set M) (t : CanonicalRV.RVSort M)
    (ht0 : t.val ≠ iRVZero) : t.val ∈ ordinaryRadiusFibre D ↔
      PaperBalls.HasRadius D (↑(Values.vrv t) : PaperBalls.Radius (M := M)) :=
  ⟨fun ⟨_,_,h⟩ => h,fun h => ⟨t.property,ht0,h⟩⟩

theorem image_definable (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T) :
    FullGammaSyntax.Scalar B {γ | ∃ i ∈ T,
      PaperBalls.HasRadius (BallImaginaries.underlying i) (↑γ.val : PaperBalls.Radius (M := M))} := by
  let U := BallImaginaries.underlying (M := M)
  let C := fun i => ordinaryRadiusFibre (U i)
  let V : Set (Values.Gamma (M := M)) := {γ | ∃ i ∈ T,
    PaperBalls.HasRadius (U i) (↑γ.val : PaperBalls.Radius (M := M))}
  have he : Values.gammaPullback V = {t | ∃ i ∈ T, t ∈ C i} := by
    ext t
    constructor
    · rintro ⟨ht,h0,i,hi,hc⟩
      exact ⟨i,hi,⟨ht,h0,hc⟩⟩
    · rintro ⟨i,hi,ht,h0,hc⟩
      exact ⟨ht,h0,i,hi,hc⟩
  have hR := relation_definable B
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hr : FullBaseAtomicity.OverBase B {z : Fin 1 → M | ∃ i ∈ T, z 0 ∈ C i} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.range
      (ImaginaryBaseFamilies.Relation.restrict hp hT hR)
  change FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ Values.gammaPullback V}
  rw [he]
  change FullBaseAtomicity.OverBase B {z : Fin 1 → M | ∃ i ∈ T, z 0 ∈ C i}
  exact hr

theorem image_finite (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (T : Set (BallImaginaries.Ball M)) (hT : T.Finite) :
    {γ : Values.Gamma (M := M) | ∃ i ∈ T,
      PaperBalls.HasRadius (BallImaginaries.underlying i) (↑γ.val : PaperBalls.Radius (M := M))}.Finite := by
  have hf (i : BallImaginaries.Ball M) : {γ : Values.Gamma (M := M) |
      PaperBalls.HasRadius (BallImaginaries.underlying i) (↑γ.val : PaperBalls.Radius (M := M))}.Subsingleton := by
    intro α hα β hβ
    apply Subtype.ext
    exact WithBot.coe_inj.mp (PaperBallInvariants.hasRadius_unique δ hδ hα hβ)
  have h := hT.biUnion (fun i _ => (hf i).finite)
  convert h using 1
  ext γ
  simp only [Set.mem_iUnion,Set.mem_setOf_eq,exists_prop]

theorem parent_test_definable (B : FullBaseAtomicity.Base (M := M))
    (γ : Values.Gamma (M := M)) (hγ : FullGammaSyntax.Scalar B {γ}) :
    FullBaseAtomicity.Family B {i |
      PaperBalls.HasRadius (BallImaginaries.underlying i) (↑γ.val : PaperBalls.Radius (M := M))} := by
  let U := BallImaginaries.underlying (M := M)
  let C := fun i => ordinaryRadiusFibre (U i)
  let F := Values.gammaPullback {γ}
  have he : {i | (C i ∩ F).Nonempty} = {i |
      PaperBalls.HasRadius (U i) (↑γ.val : PaperBalls.Radius (M := M))} := by
    ext i
    constructor
    · rintro ⟨t,htC,htF⟩
      obtain ⟨ht,h0,hval⟩ := htF
      have hc := (mem_ordinaryRadiusFibre_iff (U i) ⟨t,ht⟩ h0).mp htC
      have hv : Values.vrv ⟨t,ht⟩ = γ.val := congrArg Subtype.val
        (show Values.gammaOf ⟨t,ht⟩ h0 = γ from hval)
      rwa [hv] at hc
    · intro hc
      obtain ⟨t,h0,hval⟩ := Values.gamma_has_nonzero_representative γ
      refine ⟨t.val,?_,⟨t.property,h0,Subtype.ext hval⟩⟩
      apply (mem_ordinaryRadiusFibre_iff (U i) t h0).mpr
      rwa [hval]
  have hR := relation_definable B
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hd : FullBaseAtomicity.Family B {i | (C i ∩ F).Nonempty} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.domain
      (ImaginaryBaseFamilies.Relation.inter hp hR
        (RegionFormulas.constantRelation (A := F) hp hq hγ))
  simpa only [he] using hd

theorem value_definable (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T) (hfin : T.Finite)
    {i : BallImaginaries.Ball M} (hi : i ∈ T) (γ : Values.Gamma (M := M))
    (hc : PaperBalls.HasRadius (BallImaginaries.underlying i) (↑γ.val : PaperBalls.Radius (M := M))) :
    FullGammaSyntax.Scalar B {γ} := by
  classical
  have hf := image_finite δ hδ T hfin
  have hF : FullGammaSyntax.Scalar B (hf.toFinset : Set (Values.Gamma (M := M))) := by
    simpa only [Set.Finite.coe_toFinset] using image_definable B T hT
  exact FullGammaPoint.finset_element_definable hf.toFinset hF γ
    (hf.mem_toFinset.mpr ⟨i,hi,hc⟩)

end IntegrationInACVF.Section3ACVF.OrdinaryRadiusFibres
