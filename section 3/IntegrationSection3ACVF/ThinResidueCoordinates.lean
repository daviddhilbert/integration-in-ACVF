import IntegrationSection3ACVF.SingleBallCoordinates
import IntegrationSection3ACVF.AffineResidueDomain

/-! Proved residue-coordinate data for one actual thin component,
including its complete partial LRV graph. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.BallResidueChart

noncomputable section

namespace IntegrationInACVF.Section3ACVF.ThinResidueCoordinates

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure Chart (d : PuncturedBall M) where
  a : VFType (M := M)
  r : VFType (M := M)
  α : Values.Gamma (M := M)
  hr : Values.vfValueHom r = α.val
  parent_eq : d.parent = gammaBall a α false
  holes_eq : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true
  excluded : Finset (ModelResidue M)
  card_eq : excluded.card = d.holes.card
  body_iff : ∀ x : Point a α, x.val.val ∈ d.body ↔ coordinate a r α hr x ∉ excluded

theorem exists_chart (d : PuncturedBall M) (hd : ThinFamilyGeometry.IsThin d) : Nonempty (Chart d) := by
  obtain ⟨a,α,hParent,hHoles⟩ := hd
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  obtain ⟨F,hCard,_,hBody⟩ := ResiduePunctures.finite_holes a r α hr d hParent hHoles
  exact ⟨⟨a,r,α,hr,hParent,hHoles,F,hCard,hBody⟩⟩

def value {d : PuncturedBall M} (C : Chart d) (x : M) : ModelResidue M :=
  SingleBallCoordinates.value C.a C.r C.α C.hr x

theorem value_of_point {d : PuncturedBall M} (C : Chart d) (x : Point C.a C.α) :
    value C x.val.val = coordinate C.a C.r C.α C.hr x :=
  SingleBallCoordinates.value_of_point C.a C.r C.α C.hr x

theorem cofinite_image {d : PuncturedBall M} (C : Chart d) :
    d.body.MapsTo (value C) (Set.univ \ C.excluded) ∧
      d.body.SurjOn (value C) (Set.univ \ C.excluded) := by
  constructor
  · intro x hx
    let p : Point C.a C.α := ⟨⟨x,d.body_subset_vf hx⟩,C.parent_eq ▸ hx.1⟩
    refine ⟨Set.mem_univ _,?_⟩
    change value C p.val.val ∉ C.excluded
    rw [value_of_point]
    exact (C.body_iff p).mp hx
  · intro t ht
    obtain ⟨p,hp⟩ := BallResidueChart.surjective C.a C.r C.α C.hr t
    have hpBody := (C.body_iff p).mpr (hp.symm ▸ ht.2)
    exact ⟨p.val.val,hpBody,(value_of_point C p).trans hp⟩

theorem fibre_ball {d : PuncturedBall M} (C : Chart d) (x : M) (hx : x ∈ d.body) :
    OpenToOpenQuotient.fibre d.body (value C) (value C x) =
      BallImaginaries.underlying (ResidueBallClasses.ball C.a C.r C.α C.hr (value C x)) :=
  SingleBallCoordinates.fibre_ball C.a C.r C.α C.hr d C.parent_eq C.holes_eq x hx

def graph {d : PuncturedBall M} (C : Chart d) : Set (Fin 2 → M) :=
  AffineResidueSyntax.graph C.a C.r ∩
    ⋂ u : C.excluded, {z | z 1 ≠ (residueRV u.val).val}

theorem graph_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {d : PuncturedBall M} (C : Chart d) : (Set.univ : Set M).Definable LRV (graph C) := by
  have hTest (u : C.excluded) : (Set.univ : Set M).Definable LRV
      {z : Fin 2 → M | z 1 ≠ (residueRV u.val).val} :=
    ((Set.DefinableFun.proj LRV).ofPred_eq
      (LRV.definableFun_const (Fin 2) (Set.mem_univ (residueRV u.val).val))).compl
  exact (AffineResidueSyntax.graph_definable hc C.a C.r).inter (Set.definable_iInter_of_finite hTest)

theorem graph_iff {d : PuncturedBall M} (C : Chart d) (x : M) (t : ModelResidue M) :
    (![x,(residueRV t).val] : Fin 2 → M) ∈ graph C ↔ x ∈ d.body ∧ t = value C x := by
  have hNo : (∀ u : C.excluded, (residueRV t).val ≠ (residueRV u.val).val) ↔ t ∉ C.excluded := by
    constructor
    · intro hn ht
      exact hn ⟨t,ht⟩ rfl
    · intro hn u he
      have htu : t = u.val := residueRV_injective (Subtype.ext he)
      exact hn (htu.symm ▸ u.property)
  change ((![x,(residueRV t).val] : Fin 2 → M) ∈ AffineResidueSyntax.graph C.a C.r ∧
    (![x,(residueRV t).val] : Fin 2 → M) ∈ ⋂ u : C.excluded, {z | z 1 ≠ (residueRV u.val).val}) ↔ _
  simp only [Set.mem_iInter,Set.mem_ofPred_eq,Matrix.cons_val_one,Matrix.cons_val_zero]
  rw [hNo,AffineResidueDomain.graph_iff_point C.a C.r C.α C.hr]
  constructor
  · rintro ⟨⟨p,hpx,hpt⟩,ht⟩
    have hpBody : p.val.val ∈ d.body := (C.body_iff p).mpr (hpt.symm ▸ ht)
    have hv : value C x = t := (congrArg (value C) hpx).symm.trans ((value_of_point C p).trans hpt)
    exact ⟨hpx ▸ hpBody,hv.symm⟩
  · rintro ⟨hx,ht⟩
    let p : Point C.a C.α := ⟨⟨x,d.body_subset_vf hx⟩,C.parent_eq ▸ hx.1⟩
    have hp : coordinate C.a C.r C.α C.hr p = t := (value_of_point C p).symm.trans ht.symm
    exact ⟨⟨p,rfl,hp⟩,hp ▸ (C.body_iff p).mp hx⟩

end IntegrationInACVF.Section3ACVF.ThinResidueCoordinates
