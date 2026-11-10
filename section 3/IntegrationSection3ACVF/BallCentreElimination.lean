import IntegrationSection3ACVF.FullBallCoset
import IntegrationSection3ACVF.GammaCosetGeometry
import IntegrationSection3.FibreEqualityFormulas

/-! Elimination of one named coset-ball in favour of every one of
its real centres. The subgroup stays over the original base, and all ball
codes are quantified; no radius lift or centre becomes a named parameter. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity

namespace IntegrationInACVF.Section3ACVF.BallCentreElimination

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def centres (H : AddSubgroup (VFType (M := M))) : BallImaginaries.Ball M → Set M :=
  FibreEqualityFormulas.equalFibres (BallImaginaries.underlying (M := M))
    {x | iVF x} (cosetRelation H)

def graph (H : AddSubgroup (VFType (M := M)))
    (C : BallImaginaries.Ball M → Set M) : Set (M × M) :=
  {p | ∃ j, p.1 ∈ C j ∧ p.2 ∈ centres H j}

theorem centres_definable (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))}) :
    FullBaseAtomicity.Relation B (centres H) := by
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hu := BallPresentation.membership_definable (M := M) B.real
  have hs := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have hr := FullBallCoset.cosetRelation_definable B H hH
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact FibreEqualityFormulas.equalFibres_definable hp hq
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hu)
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hs) hr

theorem graph_definable (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))})
    {C : BallImaginaries.Ball M → Set M} (hC : FullBaseAtomicity.Relation B C) :
    FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ graph H C} := by
  have hc := centres_definable B H hH
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact FibreEqualityFormulas.compose_definable hp hC hc

theorem on_coset (H : AddSubgroup (VFType (M := M)))
    (i : BallImaginaries.Ball M) (c : VFType (M := M))
    (hi : BallImaginaries.underlying i = cosetBody H c)
    (C : BallImaginaries.Ball M → Set M) {A : Set M} (hCi : C i = A)
    (y : M) (hy : y ∈ BallImaginaries.underlying i) (x : M) :
    (x,y) ∈ graph H C ↔ x ∈ A := by
  let u : VFType (M := M) := ⟨y,BallImaginaries.underlying_subset_vf i hy⟩
  have hu : QuotientAddGroup.mk' H u = QuotientAddGroup.mk' H c :=
    (GammaCosetGeometry.cosetBody_mem H u c).mp (hi ▸ hy)
  have he : cosetBody H u = cosetBody H c := by
    change (Subtype.val '' {z | QuotientAddGroup.mk' H z = QuotientAddGroup.mk' H u}) =
      (Subtype.val '' {z | QuotientAddGroup.mk' H z = QuotientAddGroup.mk' H c})
    rw [hu]
  have hFibre : BallImaginaries.underlying i = DefinableFamilies.fibre (cosetRelation H) y :=
    hi.trans (he.symm.trans (cosetRelation_fibre H u).symm)
  have hiCent : y ∈ centres H i :=
    ⟨u.property,fun z => Set.ext_iff.mp hFibre z⟩
  constructor
  · rintro ⟨j,hx,hj⟩
    have hjFibre : BallImaginaries.underlying j = DefinableFamilies.fibre (cosetRelation H) y :=
      Set.ext hj.2
    have hji : j = i := BallImaginaries.underlying_injective (hjFibre.trans hFibre.symm)
    simpa only [hji,hCi] using hx
  · intro hx
    exact ⟨i,by simpa only [hCi] using hx,hiCent⟩

theorem adjoin_elimination (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))})
    (i : BallImaginaries.Ball M) (c : VFType (M := M))
    (hi : BallImaginaries.underlying i = cosetBody H c)
    {A : Set M} (hA : FullBaseAtomicity.OverBase (B.adjoin (Sum.inl i))
      {z : Fin 1 → M | z 0 ∈ A}) :
    ∃ G : Set (M × M),
      FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ G} ∧
        ∀ y ∈ BallImaginaries.underlying i, ∀ x, ((x,y) ∈ G ↔ x ∈ A) := by
  obtain ⟨R,hR,hRi⟩ := (FullBaseAtomicity.OverBase.adjoin_iff (B := B)
    (Sum.inl i) {z : Fin 1 → M | z 0 ∈ A}).mp hA
  let Cname := fun j : ParameterPresentation.Name (M := M) => {x : M | ![x] ∈ R j}
  let p := @ParameterPresentation.presentation M sM hM
  have hCname : FullBaseAtomicity.OverBase B (p.relationPullback Cname) := by
    apply FullBaseAtomicity.OverBase.congr hR
    intro z
    have he : (![z (.inr 0)] : Fin 1 → M) = z ∘ Sum.inr := by
      funext k
      fin_cases k
      rfl
    change (∃ hz : z ∘ Sum.inl ∈ p.codes, z ∘ Sum.inr ∈ R (p.decode ⟨z ∘ Sum.inl,hz⟩)) ↔
      ∃ hz : z ∘ Sum.inl ∈ p.codes, ![z (.inr 0)] ∈ R (p.decode ⟨z ∘ Sum.inl,hz⟩)
    simp only [he]
  let C := fun j : BallImaginaries.Ball M => Cname (Sum.inl j)
  have hC : FullBaseAtomicity.Relation B C := AdjoinBall.restrict_relation B Cname hCname
  have hCi : C i = A := by
    ext x
    change (![x] : Fin 1 → M) ∈ R (Sum.inl i) ↔ x ∈ A
    rw [hRi]
    rfl
  exact ⟨graph H C,graph_definable B H hH hC,
    fun y hy x => on_coset H i c hi C hCi y hy x⟩

end IntegrationInACVF.Section3ACVF.BallCentreElimination
