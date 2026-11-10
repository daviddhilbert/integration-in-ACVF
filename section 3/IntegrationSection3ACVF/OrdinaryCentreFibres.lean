import IntegrationSection3ACVF.PaperBallInvariants
import IntegrationSection3ACVF.FullGammaRadius

/-! Full ordinary-Gamma fibres of the valuative-centre predicate.
Uses the pinned SameScalar formula and normalization theorem on all RV
representatives, without choosing a representative in the parameter base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.OrdinaryCentreFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def fieldValueEq (z : Fin 2 → M) : Prop := iVF (z 0) ∧ SameScalar (iRv (z 0)) (z 1)

def ordinaryCentreFibre (D : Set M) : Set M :=
  {t | NonzeroRV t ∧ ∀ x ∈ D, fieldValueEq ![x,t]}

theorem fieldValueEq_definable (Q : Set M) :
    @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      {z | fieldValueEq z} := by
  let F : Set (Fin 2 → M) := {z | fieldValueEq z}
  have hs := ((@definableAt_iff_normalized_raw M sM hM Q .vf _).mp
    (@definableAt_sort M sM Q .vf)).1
  have hnorm (x : M) (hx : iVF x) :
      @iRv M (CanonicalStructure.normalize (M := M)) x = @iRv M sM x :=
    CanonicalStructure.normalize_fun Fn.rvMap ![x] (fun j => by fin_cases j; exact hx)
  let N := CanonicalStructure.normalize (M := M)
  have hS : @Set.Definable M Q LRV N (Fin 2)
      {z | @SameScalar M sM (z 0) (z 1)} := by
    have h := @same_scalar_definable M N Q
    convert h using 1
    ext z
    exact (@same_scalar_normalize M sM hM (z 0) (z 1)).symm
  letI := N
  have hr : Q.DefinableFun LRV (fun z : Fin 2 → M => iRv (z 0)) := by
    have hf : Q.DefinableFun LRV (Structure.funMap (L := LRV) Fn.rvMap) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 1 Fn.rvMap)
    exact hf.comp (fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
  have hm : Q.DefinableMap LRV (fun z : Fin 2 → M => ![iRv (z 0),z 1]) := by
    intro i
    fin_cases i
    · exact hr
    · exact Set.DefinableFun.proj LRV
  have hd := (hs.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))).inter (hS.preimage_map hm)
  change Q.Definable LRV F
  convert hd using 1
  ext z
  change (@iVF M sM (z 0) ∧ @SameScalar M sM (@iRv M sM (z 0)) (z 1)) ↔
    (@iVF M sM (z 0) ∧ @SameScalar M sM (@iRv M N (z 0)) (z 1))
  exact and_congr_right (fun hx => by rw [hnorm _ hx])

theorem fieldValueEq_iff (x : VFType (M := M)) (t : CanonicalRV.RVSort M)
    (ht0 : t.val ≠ iRVZero) :
    fieldValueEq ![x.val,t.val] ↔ Values.vfValueHom x = Values.vrv t := by
  change (iVF x.val ∧ NonzeroRV (iRv x.val) ∧ NonzeroRV t.val ∧
    iLe (iRv x.val) t.val ∧ iLe t.val (iRv x.val)) ↔
      Values.vrv (CanonicalRV.encodedRv x) = Values.vrv t
  constructor
  · rintro ⟨_,_,_,hle,hge⟩
    exact (Values.vrv_eq_iff (CanonicalRV.encodedRv x) t).mpr ⟨hle,hge⟩
  · intro he
    have hsv := (Values.vrv_eq_iff (CanonicalRV.encodedRv x) t).mp he
    have hx0 : iRv x.val ≠ iRVZero := by
      intro hz
      apply ht0
      apply (Values.vrv_eq_infinity_iff t).mp
      rw [← he]
      exact (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv x)).mpr hz
    exact ⟨x.property,⟨(CanonicalRV.encodedRv x).property,hx0⟩,⟨t.property,ht0⟩,hsv⟩

theorem mem_ordinaryCentreFibre_iff {D : Set M} (hD : D ⊆ {x | iVF x})
    (t : CanonicalRV.RVSort M) (ht0 : t.val ≠ iRVZero) :
    t.val ∈ ordinaryCentreFibre D ↔ PaperBalls.HasValuativeCentre D (Values.vrv t) := by
  have he : t.val ∈ ordinaryCentreFibre D ↔
      ∀ x : VFType (M := M), x.val ∈ D → Values.vfValueHom x = Values.vrv t := by
    constructor
    · intro h x hx
      exact (fieldValueEq_iff x t ht0).mp (h.2 x.val hx)
    · intro h
      refine ⟨⟨t.property,ht0⟩,fun x hx => ?_⟩
      exact (fieldValueEq_iff ⟨x,hD hx⟩ t ht0).mpr (h ⟨x,hD hx⟩ hx)
  rw [he]
  by_cases h0 : iVFZero ∈ D
  · rw [PaperBalls.HasValuativeCentre,if_pos h0]
    constructor
    · intro h
      have hz : Values.vfValueHom (0 : VFType (M := M)) = Values.infinity := by
        rw [map_zero]; exact Values.infinity_eq_zero.symm
      exact (h 0 h0).symm.trans hz
    · intro h
      exact (ht0 ((Values.vrv_eq_infinity_iff t).mp h)).elim
  · rw [PaperBalls.HasValuativeCentre,if_neg h0]

theorem relation_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.Relation B (fun i => ordinaryCentreFibre (BallImaginaries.underlying i)) := by
  let U := BallImaginaries.underlying (M := M)
  let C := fun i => ordinaryCentreFibre (U i)
  let E : Set (Fin 2 → M) := {z | fieldValueEq z}
  let test := @fieldValueEq M sM
  let nzp := @NonzeroRV M sM
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hU := BallPresentation.membership_definable (M := M) B.real
  have hE := fieldValueEq_definable (M := M) B.real
  have hnz : @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M)) (Fin 1)
      {z | nzp (z 0)} := by
    have h := @nonzero_rv_definable M (CanonicalStructure.normalize (M := M)) B.real
    convert h using 1
    ext z
    exact (@nonzero_rv_normalize M sM hM (z 0)).symm
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hd : FullBaseAtomicity.Relation B C := by
    letI := CanonicalStructure.normalize (M := M)
    let πU : Fin 4 ⊕ Fin 1 → (Fin 4 ⊕ Fin 1) ⊕ Fin 1 :=
      Sum.elim (fun a => .inl (.inl a)) Sum.inr
    let πE : Fin 2 → (Fin 4 ⊕ Fin 1) ⊕ Fin 1 := ![.inr 0,.inl (.inr 0)]
    have hm := ImaginaryParameters.OverBase.preimage_comp
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hU) πU
    have hv := ImaginaryParameters.OverBase.preimage_comp
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hE) πE
    have hall := ImaginaryParameters.OverBase.forall_block
      (SupportFormulas.imp_definable hp hm hv) hp
    have hproper := ImaginaryParameters.OverBase.preimage_comp
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hnz)
      (Sum.inr : Fin 1 → Fin 4 ⊕ Fin 1)
    have hcode := ImaginaryParameters.OverBase.preimage_comp
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hq)
      (Sum.inl : Fin 4 → Fin 4 ⊕ Fin 1)
    change ImaginaryParameters.OverBase (L := LRV) p B (q.relationPullback C)
    convert ImaginaryParameters.OverBase.inter hcode
      (ImaginaryParameters.OverBase.inter hproper hall hp) hp using 1
    ext z
    change (∃ hc : z ∘ Sum.inl ∈ q.codes, nzp (z (.inr 0)) ∧
        ∀ x ∈ U (q.decode ⟨z ∘ Sum.inl,hc⟩), test ![x,z (.inr 0)]) ↔
      (z ∘ Sum.inl ∈ q.codes ∧ nzp (z (.inr 0)) ∧
        ∀ t : Fin 1 → M, (∃ hc : z ∘ Sum.inl ∈ q.codes,
          t 0 ∈ U (q.decode ⟨z ∘ Sum.inl,hc⟩)) → test ![t 0,z (.inr 0)])
    constructor
    · rintro ⟨hc,hn,ha⟩
      exact ⟨hc,hn,fun t ⟨_,hx⟩ => ha (t 0) hx⟩
    · rintro ⟨hc,hn,ha⟩
      exact ⟨hc,hn,fun x hx => ha ![x] ⟨hc,hx⟩⟩
  exact hd

theorem image_definable (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T) :
    FullGammaSyntax.Scalar B
      {γ | ∃ i ∈ T, PaperBalls.HasValuativeCentre (BallImaginaries.underlying i) γ.val} := by
  let U := BallImaginaries.underlying (M := M)
  let C := fun i => ordinaryCentreFibre (U i)
  let V : Set (Values.Gamma (M := M)) :=
    {γ | ∃ i ∈ T, PaperBalls.HasValuativeCentre (U i) γ.val}
  have he : Values.gammaPullback V = {t | ∃ i ∈ T, t ∈ C i} := by
    ext t
    constructor
    · rintro ⟨ht,h0,i,hi,hc⟩
      exact ⟨i,hi,(mem_ordinaryCentreFibre_iff (BallImaginaries.underlying_subset_vf i)
        ⟨t,ht⟩ h0).mpr hc⟩
    · rintro ⟨i,hi,hc⟩
      exact ⟨hc.1.1,hc.1.2,i,hi,
        (mem_ordinaryCentreFibre_iff (BallImaginaries.underlying_subset_vf i)
          ⟨t,hc.1.1⟩ hc.1.2).mp hc⟩
  have hR := relation_definable B
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hr : FullBaseAtomicity.OverBase B {z : Fin 1 → M | ∃ i ∈ T, z 0 ∈ C i} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.range
      (ImaginaryBaseFamilies.Relation.restrict hp hT hR)
  change FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ Values.gammaPullback V}
  simpa only [he] using hr

theorem image_finite (T : Set (BallImaginaries.Ball M)) (hT : T.Finite) :
    {γ : Values.Gamma (M := M) | ∃ i ∈ T,
      PaperBalls.HasValuativeCentre (BallImaginaries.underlying i) γ.val}.Finite := by
  have hf (i : BallImaginaries.Ball M) :
      {γ : Values.Gamma (M := M) |
        PaperBalls.HasValuativeCentre (BallImaginaries.underlying i) γ.val}.Subsingleton := by
    intro α hα β hβ
    apply Subtype.ext
    exact ValuativeCentreGeometry.valuativeCentre_unique
      (BallImaginaries.underlying_subset_vf i)
      (CanonicalBallSupport.encodedBall_nonempty (BallCodeGeometry.underlying_isBall i)) hα hβ
  have h := hT.biUnion (fun i _ => (hf i).finite)
  convert h using 1
  ext γ
  simp only [Set.mem_iUnion,Set.mem_setOf_eq,exists_prop]

theorem parent_test_definable (B : FullBaseAtomicity.Base (M := M))
    (γ : Values.Gamma (M := M)) (hγ : FullGammaSyntax.Scalar B {γ}) :
    FullBaseAtomicity.Family B
      {i | PaperBalls.HasValuativeCentre (BallImaginaries.underlying i) γ.val} := by
  let U := BallImaginaries.underlying (M := M)
  let C := fun i => ordinaryCentreFibre (U i)
  let F := Values.gammaPullback {γ}
  have he : {i | (C i ∩ F).Nonempty} =
      {i | PaperBalls.HasValuativeCentre (U i) γ.val} := by
    ext i
    constructor
    · rintro ⟨t,htC,htF⟩
      obtain ⟨ht,h0,hval⟩ := htF
      have hc := (mem_ordinaryCentreFibre_iff (BallImaginaries.underlying_subset_vf i)
        ⟨t,ht⟩ h0).mp htC
      have hv : Values.vrv ⟨t,ht⟩ = γ.val := congrArg Subtype.val
        (show Values.gammaOf ⟨t,ht⟩ h0 = γ from hval)
      rw [hv] at hc
      exact hc
    · intro hc
      obtain ⟨t,h0,hval⟩ := Values.gamma_has_nonzero_representative γ
      refine ⟨t.val,?_,⟨t.property,h0,Subtype.ext hval⟩⟩
      apply (mem_ordinaryCentreFibre_iff (BallImaginaries.underlying_subset_vf i) t h0).mpr
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
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T) (hfin : T.Finite)
    {i : BallImaginaries.Ball M} (hi : i ∈ T) (γ : Values.Gamma (M := M))
    (hc : PaperBalls.HasValuativeCentre (BallImaginaries.underlying i) γ.val) :
    FullGammaSyntax.Scalar B {γ} := by
  classical
  have hf := image_finite T hfin
  have hF : FullGammaSyntax.Scalar B (hf.toFinset : Set (Values.Gamma (M := M))) := by
    simpa only [Set.Finite.coe_toFinset] using image_definable B T hT
  exact FullGammaPoint.finset_element_definable hf.toFinset hF γ
    (hf.mem_toFinset.mpr ⟨i,hi,hc⟩)

end IntegrationInACVF.Section3ACVF.OrdinaryCentreFibres
