import IntegrationSection3ACVF.Geometry

/-!
# A full real-code presentation of the existing ball imaginary

The objects are exactly `BallImaginaries.Ball` from the pinned predecessor.
Three VF coordinates encode a closed ball (including singleton and VF), or
two encode a proper open ball. A fourth coordinate selects the chart. Every
valid code is retained, including codes with different centres for one ball.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3ACVF.BallPresentation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def closedTuple (q : Fin 4 → M) : Fin 3 → M := ![q 0,q 1,q 2]
def openTuple (q : Fin 4 → M) : Fin 2 → M := ![q 0,q 1]

def codeDomain : Set (Fin 4 → M) :=
  {q | (q 3 = iVFZero ∧ ∀ i, iVF (closedTuple q i)) ∨
    (q 3 ≠ iVFZero ∧ OpenBallCodes.Proper (openTuple q))}

noncomputable def decode (q : codeDomain (M := M)) : BallImaginaries.Ball M :=
  if h : q.val 3 = iVFZero then
    BallImaginaries.ofClosed (Quotient.mk _
      (⟨closedTuple q.val,(q.property.resolve_right (fun hn => hn.1 h)).2⟩ :
        ClosedBallCodes.Code M))
  else
    BallImaginaries.ofOpen (Quotient.mk _
      (⟨openTuple q.val,(q.property.resolve_left (fun hz => h hz.1)).2⟩ :
        OpenBallCodes.Code M))

def encodeClosed (q : ClosedBallCodes.Code M) : codeDomain (M := M) :=
  ⟨![q.val 0,q.val 1,q.val 2,iVFZero],Or.inl ⟨rfl,by
    intro i
    fin_cases i <;> exact q.property _⟩⟩

def encodeOpen (q : OpenBallCodes.Code M) : codeDomain (M := M) :=
  ⟨![q.val 0,q.val 1,iVFZero,iVFOne],Or.inr ⟨by
    change iVFOne ≠ iVFZero
    intro he
    exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he),by
    have he : openTuple ![q.val 0,q.val 1,iVFZero,iVFOne] = q.val := by
      funext i; fin_cases i <;> rfl
    rw [he]
    exact q.property⟩⟩

theorem decode_encodeClosed (q : ClosedBallCodes.Code M) :
    decode (encodeClosed q) = BallImaginaries.ofClosed (Quotient.mk _ q) := by
  have he : closedTuple (encodeClosed q).val = q.val := by
    funext i; fin_cases i <;> rfl
  simp only [decode,dif_pos (show (encodeClosed q).val 3 = iVFZero from rfl)]
  congr 1
  exact congrArg (Quotient.mk _) (Subtype.ext he)

theorem decode_encodeOpen (q : OpenBallCodes.Code M) :
    decode (encodeOpen q) = BallImaginaries.ofOpen (Quotient.mk _ q) := by
  have hn : (encodeOpen q).val 3 ≠ iVFZero := by
    intro he
    exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he)
  have he : openTuple (encodeOpen q).val = q.val := by
    funext i; fin_cases i <;> rfl
  simp only [decode,dif_neg hn]
  congr 1
  exact congrArg (Quotient.mk _) (Subtype.ext he)

theorem decode_surjective : Function.Surjective (decode (M := M)) := by
  intro D
  obtain ⟨c,hc⟩ := Quotient.exists_rep D
  cases c with
  | inl C =>
    obtain ⟨q,hq⟩ := Quotient.exists_rep C
    refine ⟨encodeClosed q,?_⟩
    rw [decode_encodeClosed,hq]
    exact hc
  | inr O =>
    obtain ⟨q,hq⟩ := Quotient.exists_rep O
    refine ⟨encodeOpen q,?_⟩
    rw [decode_encodeOpen,hq]
    exact hc

noncomputable def presentation : Presentation M (BallImaginaries.Ball M) (Fin 4) :=
  ⟨codeDomain,decode,decode_surjective⟩

theorem underlying_decode (q : codeDomain (M := M)) :
    BallImaginaries.underlying (decode q) =
      if q.val 3 = iVFZero then ClosedBallCodes.rawBall (closedTuple q.val)
      else OpenBallCodes.rawBall (openTuple q.val) := by
  by_cases h : q.val 3 = iVFZero
  · rw [if_pos h]
    unfold decode
    rw [dif_pos h]
    rfl
  · rw [if_neg h]
    unfold decode
    rw [dif_neg h]
    rfl

private theorem closed_membership_sorted (Q : Set M) :
    DefinableOver Q (fun _ : Fin 4 => .vf)
      {z | z 3 ∈ ClosedBallCodes.rawBall ![z 0,z 1,z 2]} := by
  let p : Parameters Q := ⟨0,Fin.elim0,(fun _ => .vf),
    (fun i => i.elim0),(fun i => i.elim0)⟩
  refine ⟨p,ClosedBallCodes.body,ClosedBallCodes.body_sorted,?_⟩
  ext z
  have he : ClosedBallCodes.tuple ![z 0,z 1,z 2] (z 3) = z := by
    funext i; fin_cases i <;> rfl
  change ((∀ i : Fin 3, iVF (![z 0,z 1,z 2] i)) ∧ iVF (z 3) ∧
      ClosedBallCodes.body.Realize Fin.elim0
        (ClosedBallCodes.tuple ![z 0,z 1,z 2] (z 3))) ↔
    ((∀ i : Fin 4, iVF (z i)) ∧ ClosedBallCodes.body.Realize Fin.elim0 z)
  rw [he]
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  tauto

theorem codeDomain_definable (Q : Set M) :
    @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin 4) codeDomain := by
  let N := CanonicalStructure.normalize (M := M)
  have hsort : @Set.Definable₁ M Q LRV N {x | @iVF M sM x} :=
    ((definableAt_iff_normalized_raw Q .vf _).mp (definableAt_sort Q .vf)).1
  have hz : @iVFZero M N = @iVFZero M sM := CanonicalStructure.sortZero_normalize .vf
  have hzero : @Set.DefinableFun M LRV N (Fin 4) Q
      (fun _ => @iVFZero M sM) := by
    rw [← hz]
    letI := N
    exact DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have h0 := hsort.preimage_comp (fun _ : Fin 1 => (0 : Fin 4))
  have h1 := hsort.preimage_comp (fun _ : Fin 1 => (1 : Fin 4))
  have h2 := hsort.preimage_comp (fun _ : Fin 1 => (2 : Fin 4))
  have he1 := (@Set.DefinableFun.proj M LRV N (Fin 4) Q 1).ofPred_eq hzero
  have he3 := (@Set.DefinableFun.proj M LRV N (Fin 4) Q 3).ofPred_eq hzero
  convert ((he3.inter (h0.inter (h1.inter h2))).union
    (he3.compl.inter ((h0.inter h1).inter he1.compl))) using 1
  ext q
  simp only [codeDomain,closedTuple,openTuple,OpenBallCodes.Proper,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,
    Set.mem_preimage,Set.mem_compl_iff,Function.comp_apply]
    <;> tauto

theorem membership_definable (Q : Set M) :
    @Presentation.DefinableRelation LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) presentation Q BallImaginaries.underlying := by
  have hc := ((definableOver_iff_normalized_raw Q (fun _ : Fin 4 => .vf) _).mp
    (closed_membership_sorted (M := M) Q)).1
  have ho := ((definableOver_iff_normalized_raw Q (fun _ : Fin 3 => .vf) _).mp
    (OpenBallCodes.membership_definable (M := M) Q)).1
  have hdom := codeDomain_definable (M := M) Q
  let N := CanonicalStructure.normalize (M := M)
  have hz : @iVFZero M N = @iVFZero M sM := CanonicalStructure.sortZero_normalize .vf
  have hzero : @Set.DefinableFun M LRV N (Fin 4 ⊕ Fin 1) Q
      (fun _ => @iVFZero M sM) := by
    rw [← hz]
    letI := N
    exact DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  let πc : Fin 4 → Fin 4 ⊕ Fin 1 := ![.inl 0,.inl 1,.inl 2,.inr 0]
  let πo : Fin 3 → Fin 4 ⊕ Fin 1 := ![.inl 0,.inl 1,.inr 0]
  have ho' : @Set.Definable M Q LRV N (Fin 4 ⊕ Fin 1)
      {z | z (.inr 0) ∈ OpenBallCodes.rawBall (openTuple (z ∘ Sum.inl))} := by
    convert ho.preimage_comp πo using 1
    ext z
    have he : Fin.init (z ∘ πo) = openTuple (z ∘ Sum.inl) := by
      funext i; fin_cases i <;> rfl
    rw [he]
    rfl
  have hflag := (@Set.DefinableFun.proj M LRV N (Fin 4 ⊕ Fin 1) Q
    (.inl 3)).ofPred_eq hzero
  change @Set.Definable M Q LRV N (Fin 4 ⊕ Fin 1)
    (presentation.relationPullback BallImaginaries.underlying)
  convert (hdom.preimage_comp (Sum.inl : Fin 4 → Fin 4 ⊕ Fin 1)).inter
    ((hflag.inter (hc.preimage_comp πc)).union (hflag.compl.inter ho')) using 1
  ext z
  constructor
  · rintro ⟨hzcode,hx⟩
    refine ⟨hzcode,?_⟩
    have he := Set.ext_iff.mp (underlying_decode (⟨z ∘ Sum.inl,hzcode⟩ : codeDomain)) (z (.inr 0))
    by_cases hf : z (.inl 3) = @iVFZero M sM
    · left
      exact ⟨hf,by simpa only [if_pos hf,closedTuple,πc] using he.mp hx⟩
    · right
      exact ⟨hf,by simpa only [if_neg hf,openTuple,πo] using he.mp hx⟩
  · rintro ⟨hzcode,hx⟩
    refine ⟨hzcode,?_⟩
    have he := Set.ext_iff.mp (underlying_decode (⟨z ∘ Sum.inl,hzcode⟩ : codeDomain)) (z (.inr 0))
    apply he.mpr
    rcases hx with ⟨hf,hx⟩ | ⟨hf,hx⟩
    · simpa only [if_pos hf,closedTuple,πc] using hx
    · simpa only [if_neg hf,openTuple,πo] using hx

theorem presentation_definable (Q : Set M) :
    @Presentation.IsDefinable M (BallImaginaries.Ball M) (Fin 4) presentation
      LRV (CanonicalStructure.normalize (M := M)) Q :=
  Presentation.isDefinable_of_membership presentation BallImaginaries.underlying
    BallImaginaries.underlying_injective (codeDomain_definable Q) (membership_definable Q)

/-- Ordinary valuation balls restricted to the released VF sort. -/
def valuationBalls {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ) : Set (Set M) :=
  {B | B ⊆ {x | iVF x} ∧
    ValOneEC.IsKBall (RingHom.id (VFType (M := M))) v {x | x.val ∈ B}}

theorem valuationBalls_laminar {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ) : IsLaminar (valuationBalls v) := by
  intro B hB C hC
  by_cases hd : Disjoint B C
  · exact Or.inr (Or.inr hd)
  obtain ⟨x,hxB,hxC⟩ := Set.not_disjoint_iff.mp hd
  have hm : ({z : VFType (M := M) | z.val ∈ B} ∩
      {z : VFType (M := M) | z.val ∈ C}).Nonempty := ⟨⟨x,hB.1 hxB⟩,hxB,hxC⟩
  rcases ValOneEC.isKBall_subset_or_subset hB.2 hC.2 hm with h | h
  · left
    intro y hy
    exact h (a := (⟨y,hB.1 hy⟩ : VFType (M := M))) hy
  · right; left
    intro y hy
    exact h (a := (⟨y,hC.1 hy⟩ : VFType (M := M))) hy

theorem normalized_cMinimalOn_valuationBalls (Q : Set M)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y) :
    @CMinimalOn M LRV (CanonicalStructure.normalize (M := M)) Q
      {x | iVF x} (valuationBalls v) := by
  intro S hS hsub
  exact (normalized_cMinimalOn Q S hS hsub).mono fun B hB =>
    ⟨isBall_subset_vf B hB,encodedBall_isKBall v hv B hB⟩

theorem underlying_valuationBall {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (D : BallImaginaries.Ball M) : BallImaginaries.underlying D ∈ valuationBalls v := by
  refine ⟨BallImaginaries.underlying_subset_vf D,?_⟩
  obtain ⟨c,hc⟩ := Quotient.exists_rep D
  rw [← hc]
  cases c with
  | inl C =>
    obtain ⟨q,hq⟩ := Quotient.exists_rep C
    rw [← hq]
    change ValOneEC.IsKBall (RingHom.id (VFType (M := M))) v (ClosedBallCodes.ball q.val)
    by_cases hz : q.val 2 = iVFZero
    · rw [ClosedBallCodes.ball_eq_univ q.val q.property hz]
      exact .univ
    · rw [ClosedBallCodes.ball_eq_closed v hv q.val q.property hz]
      exact .closed _ _
  | inr O =>
    obtain ⟨q,hq⟩ := Quotient.exists_rep O
    rw [← hq]
    change ValOneEC.IsKBall (RingHom.id (VFType (M := M))) v (OpenBallCodes.ball q.val)
    rw [OpenBallCodes.ball_eq_open v hv q.val q.property]
    exact .openball _ _

/-- Lemma 3.2 over a real parameter base, with actual ball-imaginary indices
and actual output balls. Its function graph and all parameter tests use full
real preimages. No atomicity, C-minimality, representative or algebraicity
conclusion is assumed. Extension to a base with Gamma names is separate. -/
theorem lemma_3_2_real_base (Q : Set M) (T : Set (BallImaginaries.Ball M))
    (f : BallImaginaries.Ball M → BallImaginaries.Ball M)
    (hT : @Presentation.DefinableFamily LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) presentation Q T)
    (hf : @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin 4 ⊕ Fin 4)
      (presentation.functionPullback T f))
    (hdis : T.Pairwise fun i j => Disjoint (BallImaginaries.underlying (f i))
      (BallImaginaries.underlying (f j)))
    {i : BallImaginaries.Ball M} (hi : i ∈ T)
    (hna : ¬ @Presentation.Algebraic LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) presentation Q (f i)) :
    @Presentation.AtomicWith LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) presentation Q i (BallImaginaries.underlying (f i)) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  let C : BallImaginaries.Ball M → Set M :=
    fun j => {x | j ∈ T ∧ x ∈ BallImaginaries.underlying (f j)}
  have hC := (membership_definable Q).comp_on hf
  have hc (j : BallImaginaries.Ball M) (hj : j ∈ T) :
      C j = BallImaginaries.underlying (f j) := by
    ext x
    exact and_iff_right hj
  have hb : ∀ j ∈ T, C j ∈ valuationBalls v := by
    intro j hj
    rw [hc j hj]
    exact underlying_valuationBall v hv (f j)
  have hd : T.Pairwise fun j k => Disjoint (C j) (C k) := by
    intro j hj k hk hne
    rw [hc j hj,hc k hk]
    exact hdis hj hk hne
  have h := parametric_atomic_of_output (presentation_definable Q)
    (valuationBalls_laminar v) (normalized_cMinimalOn_valuationBalls Q v hv)
    (fun _ hb => hb.1) hT hC hb hd hf hi hna
  rw [hc i hi] at h
  exact h

end IntegrationInACVF.Section3ACVF.BallPresentation
