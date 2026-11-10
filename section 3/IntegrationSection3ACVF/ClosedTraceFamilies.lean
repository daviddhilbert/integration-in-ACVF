import IntegrationSection3ACVF.MaximalSubballFamilies
import IntegrationSection3ACVF.FullRelationSupports
import IntegrationSection3.QuotientCover

/-! Finite/cofinite intersection traces after naming a source cut.
No atomicity is asserted over the enlarged base. C-minimality gives the
trace property over that base directly. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.PuncturedGeometry

namespace IntegrationInACVF.Section3ACVF.ClosedTraceFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem named_ball_body (B : FullBaseAtomicity.Base (M := M)) (k : BallImaginaries.Ball M) :
    FullBaseAtomicity.OverBase (B.adjoin (Sum.inl k))
      {z : Fin 1 → M | z 0 ∈ BallImaginaries.underlying k} := by
  let R := fun n : ParameterPresentation.Name (M := M) =>
    {z : Fin 1 → M | z 0 ∈ ParameterPresentation.body n}
  have hm := ParameterPresentation.membership_definable (M := M) B.real
  have hR : FullBaseAtomicity.OverBase B
      (ImaginaryParameters.vectorPullback (@ParameterPresentation.presentation M sM hM) R) :=
    FullBaseAtomicity.OverBase.of_real hm
  exact (FullBaseAtomicity.OverBase.adjoin_iff (B := B) (Sum.inl k) _).mpr ⟨R,hR,rfl⟩

theorem meets_named_ball (B : FullBaseAtomicity.Base (M := M))
    {T : Set (BallImaginaries.Ball M)} (hT : FullBaseAtomicity.Family B T)
    {C : BallImaginaries.Ball M → Set M} (hC : FullBaseAtomicity.Relation B C)
    (k : BallImaginaries.Ball M) :
    FullBaseAtomicity.Family (B.adjoin (Sum.inl k))
      (QuotientCover.meets T C (BallImaginaries.underlying k)) := by
  let B' := B.adjoin (Sum.inl k)
  have hD := named_ball_body B k
  have hT' : FullBaseAtomicity.Family B' T :=
    FullBaseAtomicity.OverBase.mono hT Set.Subset.rfl (Set.subset_insert _ _)
  have hC' : FullBaseAtomicity.Relation B' C :=
    FullBaseAtomicity.OverBase.mono hC Set.Subset.rfl (Set.subset_insert _ _)
  have hp := ParameterPresentation.codeDomain_definable (M := M) B'.real
  have hq := BallPresentation.codeDomain_definable (M := M) B'.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  have hconst := RegionFormulas.constantRelation (p := p) (q := q) (B := B') hp hq hD
  have hint := ImaginaryBaseFamilies.Relation.inter hp hC' hconst
  have hdomain := ImaginaryBaseFamilies.Relation.domain hint
  exact ImaginaryBaseFamilies.Family.inter hp hT' hdomain

theorem finite_or_cofinite_native_cut {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedBall M) (hd : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ d.body})
    (α : Values.Gamma (M := M)) (b : VFType (M := M))
    (hParent : d.parent = GammaRadiusAtomicity.gammaBall b α false)
    (hholes : ∀ h ∈ d.holes, ∃ a : VFType (M := M), h = GammaRadiusAtomicity.gammaBall a α true)
    (hT : FullBaseAtomicity.Family B (MaximalSubballGeometry.classes d α))
    {C : BallImaginaries.Ball M → Set M} (hC : FullBaseAtomicity.Relation B C)
    (c t : VFType (M := M)) :
    let T := MaximalSubballGeometry.classes d α
    let E := QuotientCover.meets T (fun j => {x : VFType (M := M) | x.val ∈ C j})
      {x | v (x-c) ≤ v t}
    E.Finite ∨ (T \ E).Finite := by
  let T := MaximalSubballGeometry.classes (M := M) d α
  obtain ⟨k,hk⟩ := BallImaginaries.closed_disc_coded v hv c t
  let E := QuotientCover.meets T C (BallImaginaries.underlying k)
  have hE := meets_named_ball B hT hC k
  let B' := B.adjoin (Sum.inl k)
  have hd' : FullBaseAtomicity.OverBase B' {z : Fin 1 → M | z 0 ∈ d.body} :=
    FullBaseAtomicity.OverBase.mono hd Set.Subset.rfl (Set.subset_insert _ _)
  have hfin := MaximalSubballFamilies.finite_or_cofinite B' δ hδ d hd' α b hParent hholes
    hE (fun _ h => h.1)
  have he : QuotientCover.meets T (fun j => {x : VFType (M := M) | x.val ∈ C j})
      {x | v (x-c) ≤ v t} = E := by
    ext j
    constructor
    · rintro ⟨hj,x,hxc,hxD⟩
      exact ⟨hj,x.val,hxc,(Set.ext_iff.mp hk x).mpr hxD⟩
    · rintro ⟨hj,x,hxc,hxk⟩
      let u : VFType (M := M) := ⟨x,BallImaginaries.underlying_subset_vf k hxk⟩
      exact ⟨hj,u,hxc,(Set.ext_iff.mp hk u).mp hxk⟩
  change (QuotientCover.meets T (fun j => {x : VFType (M := M) | x.val ∈ C j})
    {x | v (x-c) ≤ v t}).Finite ∨ _
  rwa [he]

end IntegrationInACVF.Section3ACVF.ClosedTraceFamilies
