import IntegrationSection3ACVF.FullRelationSupports
import IntegrationSection3ACVF.OrdinaryRadiusFibres
import IntegrationSection3ACVF.BallKindPredicates
import IntegrationSection3ACVF.BallEnlargementGeometry
import IntegrationSection3.CoverRadiusFormulas
import IntegrationSection3.FiniteClosedHull

/-! Intrinsic hull-radius graph for the canonical inverse supports
in 3.11. Every containing ball, support ball and Gamma code is retained. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.SupportHullRadius

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "U" => @BallImaginaries.underlying M sM

def covers (R : Set (M × M)) (n : ℕ) : BallImaginaries.Ball M → Set M :=
  CoverRadiusFormulas.covers (BallImaginaries.underlying (M := M))
    (fun k => OrdinaryRadiusFibres.ordinaryRadiusFibre (BallImaginaries.underlying k))
    {k | PaperBalls.IsClosedBall (BallImaginaries.underlying k)}
    (FibreSupportFormulas.SupportMember (BallImaginaries.underlying (M := M))
      (FullRelationSupports.preimages R) n)

def order : Set (M × M) :=
  {p | @iLe M (@CanonicalStructure.normalize M sM) p.1 p.2}

/-- Greatest covering radius in the paper order: the smallest possible
closed hull in the native multiplicative valuation order. -/
def span (R : Set (M × M)) (n : ℕ) : BallImaginaries.Ball M → Set M :=
  CoverRadiusFormulas.greatest (covers R n) (order (M := M))

theorem covers_definable (B : FullBaseAtomicity.Base (M := M))
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R}) (n : ℕ) :
    FullBaseAtomicity.Relation B (covers (M := M) R n) := by
  let V := fun k => OrdinaryRadiusFibres.ordinaryRadiusFibre (U k)
  let D := {k | PaperBalls.IsClosedBall (U k)}
  have hs := FullRelationSupports.support_graph_definable B hR n
  have hv := OrdinaryRadiusFibres.relation_definable (M := M) B
  have hd := BallKindPredicates.closed_family_definable (M := M) B
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact CoverRadiusFormulas.covers_definable hp hq
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hv hd hs

theorem span_definable (B : FullBaseAtomicity.Base (M := M))
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R}) (n : ℕ) :
    FullBaseAtomicity.Relation B (span (M := M) R n) := by
  let C := covers (M := M) R n
  let le := order (M := M)
  have hc := covers_definable B hR n
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  have hle : ImaginaryParameters.OverBase (L := LRV) p B
      {z : Fin 2 → M | (z 0,z 1) ∈ le} :=
    ImaginaryParameters.OverBase.of_real (GammaParameters.raw_le_definable B.real)
  exact CoverRadiusFormulas.greatest_definable hp hc hle

theorem mem_covers_iff (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (R : Set (M × M)) (j : BallImaginaries.Ball M) {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F
      (FullRelationSupports.preimages R j))
    (t : CanonicalRV.RVSort M) (ht0 : t.val ≠ iRVZero) :
    t.val ∈ covers R F.card j ↔ ∃ k : BallImaginaries.Ball M,
      PaperBalls.IsClosedBall (BallImaginaries.underlying k) ∧
        PaperBalls.HasRadius (BallImaginaries.underlying k)
          (↑(Values.vrv t) : PaperBalls.Radius (M := M)) ∧
        ∀ b ∈ F, b ⊆ BallImaginaries.underlying k := by
  have hb := minimal_support_encoded hF
  have hcodes : ∀ b ∈ F, ∃ i, U i = b := fun b hbF => BallCodeGeometry.encodedBall_coded b (hb b hbF)
  have he (i : BallImaginaries.Ball M) : FibreSupportFormulas.SupportMember U
      (FullRelationSupports.preimages R) F.card j i ↔ U i ∈ F :=
    FibreSupportFormulas.supportMember_iff_canonical BallImaginaries.underlying_injective
      ballFamily_laminar (Or.inr rfl) (ballFamily_avoids δ hδ)
      (fun i => Or.inl (BallCodeGeometry.underlying_isBall i)) hF hcodes i
  constructor
  · rintro ⟨k,hk,ht,hall⟩
    refine ⟨k,hk,(OrdinaryRadiusFibres.mem_ordinaryRadiusFibre_iff (U k) t ht0).mp ht,?_⟩
    intro b hbF
    obtain ⟨i,hi⟩ := hcodes b hbF
    have hm : U i ∈ F := hi.symm ▸ hbF
    have hs := hall i ((he i).mpr hm)
    rwa [hi] at hs
  · rintro ⟨k,hk,hr,hall⟩
    refine ⟨k,hk,(OrdinaryRadiusFibres.mem_ordinaryRadiusFibre_iff (U k) t ht0).mpr hr,?_⟩
    intro i hi
    exact hall (U i) ((he i).mp hi)

def supportLift (F : Finset (Set M)) : Set (VFType (M := M)) :=
  {x | ∃ b ∈ F, x.val ∈ b}

theorem cover_from_hull {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (R : Set (M × M)) (j : BallImaginaries.Ball M) {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F (FullRelationSupports.preimages R j))
    (a r : VFType (M := M)) (hr : r ≠ 0)
    (hHull : FiniteClosedHull.IsHull v (supportLift F) a r) :
    (CanonicalRV.encodedRv r).val ∈ covers R F.card j := by
  have ht0 : (CanonicalRV.encodedRv r).val ≠ iRVZero :=
    fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he)
  let γ := Values.gammaOf (CanonicalRV.encodedRv r) ht0
  have hvalue : Values.vfValueHom r = γ.val := rfl
  obtain ⟨k,hk,hkClosed,hkRadius⟩ := BallEnlargementGeometry.closed_ball_coded a γ
  apply (mem_covers_iff δ hδ R j hF (CanonicalRV.encodedRv r) ht0).mpr
  refine ⟨k,hkClosed,hkRadius,?_⟩
  intro b hb x hx
  let u : VFType (M := M) := ⟨x,isBall_subset_vf b (minimal_support_encoded hF b hb) hx⟩
  have hu : u ∈ supportLift F := ⟨b,hb,hx⟩
  rw [hk]
  exact (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r γ hvalue u).mpr (hHull.1 hu)

theorem cover_value_le_hull {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (R : Set (M × M)) (j : BallImaginaries.Ball M) {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F (FullRelationSupports.preimages R j))
    (a r : VFType (M := M)) (hHull : FiniteClosedHull.IsHull v (supportLift F) a r)
    (t : CanonicalRV.RVSort M) (ht0 : t.val ≠ iRVZero) (ht : t.val ∈ covers R F.card j) :
    Values.vrv t ≤ Values.vfValueHom r := by
  obtain ⟨k,hkClosed,hkRadius,hFk⟩ := (mem_covers_iff δ hδ R j hF t ht0).mp ht
  let γ := Values.gammaOf t ht0
  obtain ⟨b,hb⟩ := BallEnlargementGeometry.closed_ordinary_presentation δ hδ hkClosed γ hkRadius
  obtain ⟨s,hs⟩ := GammaCosetGeometry.vf_representative γ
  have hsub : supportLift F ⊆ {x | v (x-b) ≤ v s} := by
    rintro x ⟨c,hc,hxc⟩
    have hx := hFk c hc hxc
    rw [hb] at hx
    exact (BallKindPredicates.gammaBall_mem_valuation_closed v hv b s γ hs x).mp hx
  have hle := hHull.2 b s hsub
  have hp := (Values.vf_pred_iff_gamma_le r s).mp ((hv r s).mpr hle)
  rwa [hs] at hp

theorem mem_span_iff_value {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (R : Set (M × M)) (j : BallImaginaries.Ball M) {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F (FullRelationSupports.preimages R j))
    (a r : VFType (M := M)) (hr : r ≠ 0)
    (hHull : FiniteClosedHull.IsHull v (supportLift F) a r)
    (t : CanonicalRV.RVSort M) (ht0 : t.val ≠ iRVZero) :
    t.val ∈ span R F.card j ↔ Values.vrv t = Values.vfValueHom r := by
  have hr0 : (CanonicalRV.encodedRv r).val ≠ iRVZero :=
    fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he)
  have hCover := cover_from_hull v hv δ hδ R j hF a r hr hHull
  constructor
  · rintro ⟨ht,hgreat⟩
    have hle := cover_value_le_hull v hv δ hδ R j hF a r hHull t ht0 ht
    have hge : Values.vfValueHom r ≤ Values.vrv t := by
      apply (Values.vrv_le_iff (CanonicalRV.encodedRv r) t).mpr
      exact (rv_le_normalize _ _ (CanonicalRV.encodedRv r).property t.property).mp (hgreat _ hCover)
    exact le_antisymm hle hge
  · intro he
    have htCover : t.val ∈ covers R F.card j := by
      obtain ⟨k,hk,hkr,hFcov⟩ :=
        (mem_covers_iff δ hδ R j hF (CanonicalRV.encodedRv r) hr0).mp hCover
      apply (mem_covers_iff δ hδ R j hF t ht0).mpr
      refine ⟨k,hk,?_,hFcov⟩
      rwa [he]
    refine ⟨htCover,?_⟩
    intro s hs
    have hsp : GammaParameters.NonzeroRV s := by
      obtain ⟨k,_,hsV,_⟩ := hs
      exact ⟨hsV.choose,hsV.choose_spec.1⟩
    have hle := cover_value_le_hull v hv δ hδ R j hF a r hHull ⟨s,hsp.1⟩ hsp.2 hs
    change @iLe M (@CanonicalStructure.normalize M sM) s t.val
    apply (rv_le_normalize s t.val hsp.1 t.property).mpr
    apply (Values.vrv_le_iff ⟨s,hsp.1⟩ t).mp
    rwa [he]

theorem span_eq_gammaFibre {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (R : Set (M × M)) (j : BallImaginaries.Ball M) {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F (FullRelationSupports.preimages R j))
    (a r : VFType (M := M)) (hr : r ≠ 0)
    (hHull : FiniteClosedHull.IsHull v (supportLift F) a r) :
    let γ := Values.gammaOf (CanonicalRV.encodedRv r)
      (fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he))
    span R F.card j = Values.gammaPullback {γ} := by
  let γ := Values.gammaOf (CanonicalRV.encodedRv r)
    (fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he))
  change span R F.card j = Values.gammaPullback {γ}
  ext t
  constructor
  · intro ht
    have hsp : GammaParameters.NonzeroRV t := by
      obtain ⟨k,_,htV,_⟩ := ht.1
      exact ⟨htV.choose,htV.choose_spec.1⟩
    refine ⟨hsp.1,hsp.2,?_⟩
    apply Subtype.ext
    exact (mem_span_iff_value v hv δ hδ R j hF a r hr hHull ⟨t,hsp.1⟩ hsp.2).mp ht
  · rintro ⟨htRV,ht0,htγ⟩
    apply (mem_span_iff_value v hv δ hδ R j hF a r hr hHull ⟨t,htRV⟩ ht0).mpr
    exact congrArg Subtype.val (show Values.gammaOf ⟨t,htRV⟩ ht0 = γ from htγ)

end IntegrationInACVF.Section3ACVF.SupportHullRadius
