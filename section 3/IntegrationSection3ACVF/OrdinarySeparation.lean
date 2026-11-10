import IntegrationSection3ACVF.UniformSupportHull
import IntegrationSection3ACVF.ClosedTraceFamilies
import IntegrationSection3ACVF.InfiniteOrdinaryBalls
import IntegrationSection3.RelationProjections
import IntegrationSection3.UniformHullSeparation

/-! Geometric separation for corrected 3.11, in ordinary ball
presentations. The target may have any finite family of maximal open holes.
The invariant radius is intrinsic, and the closed cut is named only for
the C-minimal finite/cofinite trace argument. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.OrdinarySeparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "U" => @BallImaginaries.underlying M sM

theorem not_finite_rows (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (i : BallImaginaries.Ball M) (hi : AdjoinBall.AtomicOver B (BallImaginaries.underlying i))
    (c : VFType (M := M)) (σ : Values.Gamma (M := M))
    (hsource : BallImaginaries.underlying i = gammaBall c σ true)
    (d : PuncturedBall M) (hd : AdjoinBall.AtomicOver B d.body)
    (b : VFType (M := M)) (α : Values.Gamma (M := M))
    (hα : FullGammaSyntax.Scalar B {α})
    (hParent : d.parent = gammaBall b α false)
    (hholes : ∀ h ∈ d.holes, ∃ a : VFType (M := M), h = gammaBall a α true)
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    (hRsub : R ⊆ BallImaginaries.underlying i ×ˢ d.body) (hne : R.Nonempty) :
    ¬ (∀ x ∈ BallImaginaries.underlying i, {y | (x,y) ∈ R}.Finite) := by
  classical
  intro hfinite
  let T := MaximalSubballGeometry.classes (M := M) d α
  let C := FullRelationSupports.preimages (M := M) R
  have hRsource (x y : M) (hxy : (x,y) ∈ R) : x ∈ U i := (hRsub hxy).1
  have hproj : (∀ x ∈ U i, ∃ y ∈ d.body, (x,y) ∈ R) ∧
      (∀ y ∈ d.body, ∃ x ∈ U i, (x,y) ∈ R) := by
    let p := @ParameterPresentation.presentation M sM hM
    letI := CanonicalStructure.normalize (M := M)
    exact RelationProjections.surjective hi.2 hd.2 hR hRsub hne
  have hT := MaximalSubballFamilies.classes_definable B d hd.1 α hα
  have hTinf := MaximalSubballGeometry.classes_infinite δ hδ1 d α b hParent hholes
  have hTsub (j : BallImaginaries.Ball M) (hj : j ∈ T) : U j ⊆ d.body := hj.2
  have hTdis := MaximalSubballGeometry.classes_disjoint δ hδ1 d α
  obtain ⟨F,hF,hproper⟩ := FullRelationSupports.exists_proper_inverse_supports B δ hδ1
    i hi hR hRsource hfinite hd.2 hT hTinf hTsub hTdis
  have hCsub (j : BallImaginaries.Ball M) (_ : j ∈ T) : C j ⊆ U i := by
    rintro x ⟨y,hxy,_⟩
    exact hRsource x y hxy
  have hCVF (j : BallImaginaries.Ball M) (hj : j ∈ T) : C j ⊆ {x | iVF x} :=
    (hCsub j hj).trans (BallImaginaries.underlying_subset_vf i)
  have hCinf (j : BallImaginaries.Ball M) (hj : j ∈ T) : (C j).Infinite := by
    obtain ⟨a,ha⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ1 hj.1.1 α hj.1.2
    have hUinf : (U j).Infinite := by rw [ha]; exact InfiniteOrdinaryBalls.open_infinite h00 δ hδ1 a α
    exact UniformSupportHull.preimage_infinite R hRsource hfinite j hUinf
      (fun y hy => hproj.2 y (hTsub j hj hy))
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨s,hs⟩ := GammaCosetGeometry.vf_representative σ
  have hs0 : s ≠ 0 := by
    intro he
    have hzero : Values.vfValueHom s = Values.infinity := by
      rw [he,map_zero]
      exact Values.infinity_eq_zero.symm
    exact σ.property (hs.symm.trans hzero)
  have hSourceNative (x : VFType (M := M)) : x.val ∈ U i ↔ v (x-c) < v s := by
    rw [hsource]
    exact GammaCosetGeometry.gammaBall_mem_valuation v hv c s σ hs x
  have hproperNative (j : BallImaginaries.Ball M) (hj : j ∈ T) (D : Set M) (hD : D ∈ F j) :
      {x : VFType (M := M) | x.val ∈ D} ⊂ {x | v (x-c) < v s} := by
    refine ⟨fun x hx => (hSourceNative x).mp ((hproper j hj D hD).1 hx),?_⟩
    intro hrev
    apply (hproper j hj D hD).2
    intro x hx
    let u : VFType (M := M) := ⟨x,BallImaginaries.underlying_subset_vf i hx⟩
    exact hrev ((hSourceNative u).mp hx)
  obtain ⟨ρ,hρ⟩ := UniformSupportHull.common_hull_radius v hv B h00 δ hδ hδ1 hR hd hT
    hTinf.nonempty hTsub hTdis F hF c s hs0 hproperNative hCVF hCinf
  obtain ⟨j0,hj0⟩ := hTinf.nonempty
  obtain ⟨a0,r0,hr0,hHull0,hr0s,hval0⟩ := hρ j0 hj0
  let Cnative := fun j : BallImaginaries.Ball M => {x : VFType (M := M) | x.val ∈ C j}
  have hsubNative (j : BallImaginaries.Ball M) (hj : j ∈ T) :
      Cnative j ⊆ {x | v (x-c) < v s} := fun x hx => (hSourceNative x).mp (hCsub j hj hx)
  have hcoverNative (x : VFType (M := M)) (hx : v (x-c) < v s) :
      ∃ j ∈ T, x ∈ Cnative j := by
    obtain ⟨y,hy,hxy⟩ := hproj.1 x.val ((hSourceNative x).mpr hx)
    obtain ⟨j,hj,hyj⟩ := MaximalSubballGeometry.covers_body d α b hParent hholes y hy
    exact ⟨j,hj,y,hxy,hyj⟩
  have hhull (j : BallImaginaries.Ball M) (hj : j ∈ T) :
      ∃ a : VFType (M := M), Cnative j ⊆ {x | v (x-a) ≤ v r0} := by
    obtain ⟨a,r,hr,hHull,hrsmall,hval⟩ := hρ j hj
    have hrr0 : v r = v r0 := (Values.vf_value_eq_iff v hv r r0).mp (hval.trans hval0.symm)
    refine ⟨a,?_⟩
    intro x hx
    have hxHull := hHull.1 (UniformSupportHull.preimage_subset_supportLift (hF j hj) (hCVF j hj) hx)
    rwa [hrr0] at hxHull
  have htrace (t : VFType (M := M)) (_ : v t < v s) :
      (QuotientCover.meets T Cnative {x | v (x-c) ≤ v t}).Finite ∨
        (T \ QuotientCover.meets T Cnative {x | v (x-c) ≤ v t}).Finite :=
    ClosedTraceFamilies.finite_or_cofinite_native_cut v hv B δ hδ1 d hd.1 α b hParent hholes
      hT (FullRelationSupports.preimages_definable B hR) c t
  exact UniformHullSeparation.impossible v (BallRadiusGeometry.valuation_dense v hv δ hδ1)
    (GammaCosetGeometry.valuation_nat_unit h00 v hv) c s r0 hr0s T Cnative
    hsubNative hcoverNative hhull htrace

/-- The target's ordinary radius need not already be named in the base.
Checked 3.3 permits its temporary adjunction for the whole argument. -/
theorem not_finite_rows_unnamed_radius (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (i : BallImaginaries.Ball M) (hi : AdjoinBall.AtomicOver B (BallImaginaries.underlying i))
    (c : VFType (M := M)) (σ : Values.Gamma (M := M))
    (hsource : BallImaginaries.underlying i = gammaBall c σ true)
    (d : PuncturedBall M) (hd : AdjoinBall.AtomicOver B d.body)
    (b : VFType (M := M)) (α : Values.Gamma (M := M))
    (hParent : d.parent = gammaBall b α false)
    (hholes : ∀ h ∈ d.holes, ∃ a : VFType (M := M), h = gammaBall a α true)
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    (hRsub : R ⊆ BallImaginaries.underlying i ×ˢ d.body) (hne : R.Nonempty) :
    ¬ (∀ x ∈ BallImaginaries.underlying i, {y | (x,y) ∈ R}.Finite) := by
  let Bα := B.adjoin (Sum.inr α)
  have hiα := FullGammaAtomicity.lemma_3_3_one_unary h00 B δ hδ hδ1 hi α
  have hdα := FullGammaAtomicity.lemma_3_3_one_unary h00 B δ hδ hδ1 hd α
  have hδα : FullGammaSyntax.Scalar Bα {δ} :=
    FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl (Set.subset_insert _ _)
  have hα : FullGammaSyntax.Scalar Bα {α} :=
    AdjoinGamma.named_scalar α (Set.mem_insert _ _)
  have hRα : FullBaseAtomicity.OverBase Bα {z : Fin 2 → M | (z 0,z 1) ∈ R} :=
    FullBaseAtomicity.OverBase.mono hR Set.Subset.rfl (Set.subset_insert _ _)
  exact not_finite_rows Bα h00 δ hδα hδ1 i hiα c σ hsource d hdα b α hα
    hParent hholes hRα hRsub hne

end IntegrationInACVF.Section3ACVF.OrdinarySeparation
