import IntegrationSection3ACVF.BallEnlargementGeometry
import IntegrationSection3ACVF.AffineArithmetic
import IntegrationSection3ACVF.OrdinaryRadiusFibres
import IntegrationSection3ACVF.CanonicalHoles
import IntegrationSection3.AffineHoleClosure
import IntegrationSection3.AffineHoleFormulas
import IntegrationSection3.DefinableHoleRefinement

/-! Geometry for the intrinsic finite affine-hole graph. Choices in
these finiteness proofs do not enter the graph or the parameter base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity

namespace IntegrationInACVF.Section3ACVF.AffineHoleGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "U" => @BallImaginaries.underlying M sM

def radiusClass (α : Values.Gamma (M := M)) : Set (BallImaginaries.Ball M) :=
  {k | PaperBalls.IsOpenBall (BallImaginaries.underlying k) ∧
    PaperBalls.HasRadius (BallImaginaries.underlying k)
      (↑α.val : PaperBalls.Radius (M := M))}

theorem open_ordinary_presentation (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {D : Set M} (hD : PaperBalls.IsOpenBall D) (α : Values.Gamma (M := M))
    (hr : PaperBalls.HasRadius D (↑α.val : PaperBalls.Radius (M := M))) :
    ∃ a : VFType (M := M), D = gammaBall a α true := by
  rcases hD with hVF | ⟨a,β,ha⟩
  · have he := PaperBallInvariants.hasRadius_unique δ hδ hr (Or.inl ⟨hVF,rfl⟩)
    exact (WithBot.coe_ne_bot he).elim
  · have he := PaperBallInvariants.hasRadius_unique δ hδ hr
      (Or.inr (Or.inr ⟨a,β,true,ha,rfl⟩))
    have hαβ : α = β := Subtype.ext (WithBot.coe_inj.mp he)
    exact ⟨a,hαβ.symm ▸ ha⟩

theorem coset_presentation (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (α : Values.Gamma (M := M)) (H : AddSubgroup (VFType (M := M)))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a α true)
    (k : BallImaginaries.Ball M) (hk : k ∈ radiusClass α) :
    ∃ a : VFType (M := M), BallImaginaries.underlying k = cosetBody H a := by
  obtain ⟨a,ha⟩ := open_ordinary_presentation δ hδ hk.1 α hk.2
  exact ⟨a,ha.trans (hH a).symm⟩

theorem class_eq_of_mem (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (α : Values.Gamma (M := M)) (H : AddSubgroup (VFType (M := M)))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a α true)
    (k : BallImaginaries.Ball M) (hk : k ∈ radiusClass α)
    (x y : VFType (M := M)) (hx : x.val ∈ BallImaginaries.underlying k)
    (hy : y.val ∈ BallImaginaries.underlying k) :
    QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y := by
  obtain ⟨a,ha⟩ := coset_presentation δ hδ α H hH k hk
  rw [ha] at hx hy
  exact ((GammaCosetGeometry.cosetBody_mem H x a).mp hx).trans
    ((GammaCosetGeometry.cosetBody_mem H y a).mp hy).symm

theorem same_name_of_class (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (α : Values.Gamma (M := M)) (H : AddSubgroup (VFType (M := M)))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a α true)
    (k l : BallImaginaries.Ball M) (hk : k ∈ radiusClass α) (hl : l ∈ radiusClass α)
    (x y : VFType (M := M)) (hx : x.val ∈ BallImaginaries.underlying k)
    (hy : y.val ∈ BallImaginaries.underlying l)
    (he : QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y) : k = l := by
  obtain ⟨a,ha⟩ := coset_presentation δ hδ α H hH k hk
  obtain ⟨b,hb⟩ := coset_presentation δ hδ α H hH l hl
  rw [ha] at hx
  rw [hb] at hy
  have hab := ((GammaCosetGeometry.cosetBody_mem H x a).mp hx).symm.trans
    (he.trans ((GammaCosetGeometry.cosetBody_mem H y b).mp hy))
  apply BallImaginaries.underlying_injective
  rw [ha,hb]
  ext z
  constructor
  · rintro ⟨u,hu,huz⟩
    exact ⟨u,hu.trans hab,huz⟩
  · rintro ⟨u,hu,huz⟩
    exact ⟨u,hu.trans hab.symm,huz⟩

/-- Representative independence makes the output name unique for fixed
input holes and an integer. This supplies finiteness without naming either
input hole in the defining parameter base. -/
theorem affine_output_unique (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (α : Values.Gamma (M := M)) (H : AddSubgroup (VFType (M := M)))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a α true)
    (h l k k' : BallImaginaries.Ball M)
    (hh : h ∈ radiusClass α) (hl : l ∈ radiusClass α)
    (hk : k ∈ radiusClass α) (hk' : k' ∈ radiusClass α) (n : ℕ)
    (a b z a' b' z' : VFType (M := M))
    (ha : a.val ∈ BallImaginaries.underlying h) (hb : b.val ∈ BallImaginaries.underlying l)
    (hz : z.val ∈ BallImaginaries.underlying k)
    (ha' : a'.val ∈ BallImaginaries.underlying h) (hb' : b'.val ∈ BallImaginaries.underlying l)
    (hz' : z'.val ∈ BallImaginaries.underlying k')
    (he : z = AffineHoleCosets.affine a b n) (he' : z' = AffineHoleCosets.affine a' b' n) :
    k = k' := by
  apply same_name_of_class δ hδ α H hH k k' hk hk' z z' hz hz'
  rw [he,he',AffineHoleClosure.mk_step,AffineHoleClosure.mk_step,
    class_eq_of_mem δ hδ α H hH h hh a a' ha ha',
    class_eq_of_mem δ hδ α H hH l hl b b' hb hb']

theorem radiusClass_definable (B : FullBaseAtomicity.Base (M := M))
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α}) :
    FullBaseAtomicity.Family B (radiusClass α) := by
  let D := radiusClass (M := M) α
  have ho := BallKindPredicates.open_family_definable (M := M) B
  have hr := OrdinaryRadiusFibres.parent_test_definable B α hα
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryBaseFamilies.Family.inter hp ho hr

def expansion (F : Finset (Set M)) (α : Values.Gamma (M := M)) (N : ℕ)
    (h p k : BallImaginaries.Ball M) : Prop :=
  AffineHoleFormulas.expansion (BallImaginaries.underlying (M := M)) (radiusClass α)
    (DefinableHoleRefinement.original F (BallImaginaries.underlying (M := M)))
    (fun n : Fin (N+1) => AffineArithmetic.graph n.val) h p k

theorem expansion_definable (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport (CanonicalBallSupport.ballFamily (M := M)) F A)
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α}) (N : ℕ) :
    FullBaseAtomicity.OverBase B
      ((ImaginaryParameters.tuplePresentation (@BallPresentation.presentation M sM hM) (Fin 3)).pullback
        {a | expansion F α N (a 0) (a 1) (a 2)}) := by
  let E := expansion (M := M) F α N
  let R := DefinableHoleRefinement.original F U
  let D := radiusClass (M := M) α
  let Arithmetic : Fin (N+1) → Set (Fin 3 → M) := fun n => AffineArithmetic.graph n.val
  have hD := radiusClass_definable B α hα
  have hR := CanonicalHoles.holes_definable B δ hδ hA hF
  have hArithmetic (n : Fin (N+1)) := AffineArithmetic.graph_overBase B n.val
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.presentation_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact AffineHoleFormulas.expansion_definable (D := D) (R := R) (A := Arithmetic) hp hq
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hD hR hArithmetic

theorem additional_names_finite (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α})
    (F : Finset (Set M)) (N : ℕ) (p : BallImaginaries.Ball M) :
    {k | PunctureFormulas.transported
      (DefinableHoleRefinement.original F (BallImaginaries.underlying (M := M)))
      (expansion F α N) k p}.Finite := by
  let D := radiusClass (M := M) α
  let I := {h : BallImaginaries.Ball M | DefinableHoleRefinement.original F U h p}
  have hI : I.Finite := (PuncturedDecomposition.holes F (U p)).finite_toSet.preimage
    BallImaginaries.underlying_injective.injOn
  obtain ⟨H,_,hH⟩ := FullGammaRadius.gamma_subgroup B α hα true
  let C := fun (h l : BallImaginaries.Ball M) (n : Fin (N+1)) =>
    {k : BallImaginaries.Ball M | h ∈ D ∧ l ∈ D ∧ k ∈ D ∧
      ∃ x : Fin 3 → M, (∀ i, x i ∈ U ((![h,l,k] : Fin 3 → BallImaginaries.Ball M) i)) ∧
        x ∈ AffineArithmetic.graph n.val}
  have hC (h l : BallImaginaries.Ball M) (n : Fin (N+1)) : (C h l n).Subsingleton := by
    rintro k ⟨hh,hl,hk,x,hx,hAr⟩ k' ⟨_,_,hk',x',hx',hAr'⟩
    let w (i : Fin 3) : VFType (M := M) :=
      ⟨x i,BallImaginaries.underlying_subset_vf _ (hx i)⟩
    let w' (i : Fin 3) : VFType (M := M) :=
      ⟨x' i,BallImaginaries.underlying_subset_vf _ (hx' i)⟩
    have he : w 2 = AffineHoleCosets.affine (w 0) (w 1) n.val := by
      apply (AffineArithmetic.mem_graph_iff n.val (w 0) (w 1) (w 2)).mp
      convert hAr using 1
      ext i
      fin_cases i <;> rfl
    have he' : w' 2 = AffineHoleCosets.affine (w' 0) (w' 1) n.val := by
      apply (AffineArithmetic.mem_graph_iff n.val (w' 0) (w' 1) (w' 2)).mp
      convert hAr' using 1
      ext i
      fin_cases i <;> rfl
    exact affine_output_unique δ hδ α H hH h l k k' hh hl hk hk' n.val
      (w 0) (w 1) (w 2) (w' 0) (w' 1) (w' 2)
      (hx 0) (hx 1) (hx 2) (hx' 0) (hx' 1) (hx' 2) he he'
  have hf := hI.biUnion (fun h _ => hI.biUnion (fun l _ =>
    (Set.finite_univ : (Set.univ : Set (Fin (N+1))).Finite).biUnion
      (fun n _ => (hC h l n).finite)))
  apply hf.subset
  rintro k ⟨h,hh,hhD,hkD,hkp,l,hl,hlD,hne,n,x,hx,hAr⟩
  simp only [Set.mem_iUnion,exists_prop,Set.mem_univ,true_and]
  exact ⟨h,hh,l,hl,n,hhD,hlD,hkD,x,hx,hAr⟩

/-- Two distinct maximal-hole classes produce an affine output outside
the finite old family. The finite bound may be chosen from this one parent;
the resulting fixed natural number is then used in the definable graph for
all parents. It is not a new parameter. -/
theorem exists_additional_hole (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α})
    (F : Finset (Set M)) (p : BallImaginaries.Ball M)
    (c : VFType (M := M)) (hp : BallImaginaries.underlying p = gammaBall c α false)
    (hholes : ∀ d ∈ PuncturedDecomposition.holes F (BallImaginaries.underlying p),
      ∃ a : VFType (M := M), d = gammaBall a α true)
    (h l : BallImaginaries.Ball M)
    (hh : DefinableHoleRefinement.original F (BallImaginaries.underlying (M := M)) h p)
    (hl : DefinableHoleRefinement.original F (BallImaginaries.underlying (M := M)) l p)
    (hne : h ≠ l) :
    ∃ N : ℕ, ∃ k : BallImaginaries.Ball M,
      expansion F α N h p k ∧
        ∀ d ∈ PuncturedDecomposition.holes F (BallImaginaries.underlying p),
          ¬ BallImaginaries.underlying k ⊆ d := by
  let I := {j : BallImaginaries.Ball M | DefinableHoleRefinement.original F U j p}
  have hI : I.Finite := (PuncturedDecomposition.holes F (U p)).finite_toSet.preimage
    BallImaginaries.underlying_injective.injOn
  have hD (j : BallImaginaries.Ball M) (hj : j ∈ I) : j ∈ radiusClass α := by
    obtain ⟨a,ha⟩ := hholes (U j) hj
    exact ⟨Or.inr ⟨a,α,ha⟩,Or.inr (Or.inr ⟨a,α,true,ha,rfl⟩)⟩
  obtain ⟨H,_,hH⟩ := FullGammaRadius.gamma_subgroup B α hα true
  let Q := VFType (M := M) ⧸ H
  let C (j : BallImaginaries.Ball M) : Set Q :=
    {q | ∃ x : VFType (M := M), x.val ∈ U j ∧ QuotientAddGroup.mk' H x = q}
  have hC (j : BallImaginaries.Ball M) (hj : j ∈ I) : (C j).Subsingleton := by
    rintro q ⟨x,hx,rfl⟩ q' ⟨y,hy,rfl⟩
    exact class_eq_of_mem δ hδ α H hH j (hD j hj) x y hx hy
  have hT := hI.biUnion (fun j hj => (hC j hj).finite)
  let T := hT.toFinset
  have hTmem (x : VFType (M := M)) : QuotientAddGroup.mk' H x ∈ T ↔
      ∃ j ∈ I, x.val ∈ U j := by
    rw [hT.mem_toFinset]
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,exists_prop]
    constructor
    · rintro ⟨j,hj,y,hy,hyx⟩
      obtain ⟨a,ha⟩ := coset_presentation δ hδ α H hH j (hD j hj)
      refine ⟨j,hj,?_⟩
      rw [ha] at hy ⊢
      exact (GammaCosetGeometry.cosetBody_mem H x a).mpr
        (hyx.symm.trans ((GammaCosetGeometry.cosetBody_mem H y a).mp hy))
    · rintro ⟨j,hj,hx⟩
      exact ⟨j,hj,x,hx,rfl⟩
  obtain ⟨a,ha⟩ := open_ordinary_presentation δ hδ (hD h hh).1 α (hD h hh).2
  obtain ⟨b,hb⟩ := open_ordinary_presentation δ hδ (hD l hl).1 α (hD l hl).2
  have ham : a.val ∈ U h := ha.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem a α true
  have hbm : b.val ∈ U l := hb.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem b α true
  have hab : QuotientAddGroup.mk' H a ≠ QuotientAddGroup.mk' H b := by
    intro he
    exact hne (same_name_of_class δ hδ α H hH h l (hD h hh) (hD l hl) a b ham hbm he)
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  have hunit := GammaCosetGeometry.valuation_nat_unit h00 v hv
  have hHm (x : VFType (M := M)) : x ∈ H ↔ v x < v r := by
    have h0 : x ∈ H ↔ x.val ∈ cosetBody H 0 := by
      rw [GammaCosetGeometry.cosetBody_mem]
      constructor
      · intro hx
        exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa only [sub_zero] using hx)
      · intro he
        simpa only [sub_zero] using (QuotientAddGroup.eq_iff_sub_mem.mp he)
    rw [hH 0] at h0
    simpa only [sub_zero] using h0.trans
      (GammaCosetGeometry.gammaBall_mem_valuation v hv 0 r α hr x)
  have hac : v (a-c) ≤ v r :=
    (BallKindPredicates.gammaBall_mem_valuation_closed v hv c r α hr a).mp
      (hp ▸ (PuncturedDecomposition.mem_holes.mp hh).2.1.1 ham)
  have hbc : v (b-c) ≤ v r :=
    (BallKindPredicates.gammaBall_mem_valuation_closed v hv c r α hr b).mp
      (hp ▸ (PuncturedDecomposition.mem_holes.mp hl).2.1.1 hbm)
  have hba : v (b-a) = v r := by
    apply le_antisymm
    · have he : b-a = (b-c)-(a-c) := by ring
      rw [he]
      exact (v.map_sub _ _).trans (max_le hbc hac)
    · apply le_of_not_gt
      intro hlt
      have he : QuotientAddGroup.mk' H b = QuotientAddGroup.mk' H a :=
        QuotientAddGroup.eq_iff_sub_mem.mpr ((hHm _).mpr hlt)
      exact hab he.symm
  obtain ⟨n,hn,hnew⟩ := AffineHoleCosets.exists_new_coset v hunit H r a b hHm hba T T.card le_rfl
  let z := AffineHoleCosets.affine a b n
  obtain ⟨k,hk⟩ := GammaCosetGeometry.gammaBall_coded z α
  have hkD : k ∈ radiusClass α :=
    ⟨Or.inr ⟨z,α,hk⟩,Or.inr (Or.inr ⟨z,α,true,hk,rfl⟩)⟩
  have hzc : z.val ∈ gammaBall c α false :=
    (BallKindPredicates.gammaBall_mem_valuation_closed v hv c r α hr z).mpr
      (AffineHoleClosure.affine_mem_closed_parent v hunit r c a b hac hbc n)
  have hkp : U k ⊂ U p := by
    rw [hk,hp]
    exact BallEnlargementGeometry.open_inside_closed_same_radius z c α hzc
  have hzk : z.val ∈ U k := hk.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem z α true
  refine ⟨T.card,k,?_,?_⟩
  · refine ⟨hD h hh,hkD,hkp,l,hl,hD l hl,hne,⟨n,Nat.lt_succ_of_le hn⟩,
      ![a.val,b.val,z.val],?_,?_⟩
    · intro i
      fin_cases i
      · exact ham
      · exact hbm
      · exact hzk
    · exact (AffineArithmetic.mem_graph_iff n a b z).mpr rfl
  · intro d hd hsub
    obtain ⟨j,hj⟩ := BallCodeGeometry.encodedBall_coded d (by
      obtain ⟨t,ht⟩ := hholes d hd
      rw [ht]
      exact BallEnlargementGeometry.gammaBall_isBall t α true)
    have hjI : j ∈ I := by
      change U j ∈ PuncturedDecomposition.holes F (U p)
      rwa [hj]
    exact hnew ((hTmem z).mpr ⟨j,hjI,by rw [hj]; exact hsub hzk⟩)

end IntegrationInACVF.Section3ACVF.AffineHoleGeometry
