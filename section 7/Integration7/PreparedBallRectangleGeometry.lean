module

public import Integration7.PreparedUnaryBallFibres
public import IntegrationSection4.InverseOneCells
public import IntegrationSection4.BalancedFibres
public import IntegrationSection3ACVF.OpenBallRVGeometry
public import Section3.RVOperations
public import Integration7.RVLabelRectangularFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Different inverse-special balls give rectangle pieces of a balanced
relation. These statements concern the actual inverse fibres, including
their singleton degeneracy, and do not assume atomicity of the balls. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem rv_sub_reverse_congr {x y z : VFType (M := M)}
    (h : rv (x-z) = rv (y-z)) : rv (z-x) = rv (z-y) := by
  have hRaw : iRv (x-z).val = iRv (y-z).val := congrArg Subtype.val h
  have hm := congrArg (iRVMul (iRv (-1 : VFType (M := M)).val)) hRaw
  have hmul (u : VFType (M := M)) : iRv (-u).val =
      iRVMul (iRv (-1 : VFType (M := M)).val) (iRv u.val) := by
    have h := rv_mul_hom_of_model hM (-1 : VFType (M := M)).property u.property
    change iRv ((-1 : VFType (M := M))*u).val = _ at h
    simpa only [neg_one_mul] using h
  rw [← hmul,← hmul,neg_sub,neg_sub] at hm
  exact Subtype.ext hm

theorem disjoint_one_cells_rv_difference_constant
    {D E : Set (VF (M := M))} (hD : Cells.IsOneCell D) (hE : Cells.IsOneCell E)
    (hDE : Disjoint D E) {x x' y y' : VF (M := M)}
    (hx : x ∈ D) (hx' : x' ∈ D) (hy : y ∈ E) (hy' : y' ∈ E) :
    rv (y-x) = rv (y'-x') := by
  have hFirst : rv (y-x) = rv (y-x') := by
    rcases hD with ⟨c,hc⟩ | ⟨ho,_⟩
    · have he : x = x' := (hc ▸ hx).trans (hc ▸ hx').symm
      rw [he]
    · apply rv_sub_reverse_congr
      apply Subtype.ext
      exact OpenBallRVGeometry.rv_sub_constant ho y x x'
        (by rintro ⟨u,hu,he⟩; exact Set.disjoint_left.mp hDE hu ((Subtype.ext he).symm ▸ hy))
        ⟨x,hx,rfl⟩ ⟨x',hx',rfl⟩
  have hSecond : rv (y-x') = rv (y'-x') := by
    rcases hE with ⟨c,hc⟩ | ⟨ho,_⟩
    · have he : y = y' := (hc ▸ hy).trans (hc ▸ hy').symm
      rw [he]
    · apply Subtype.ext
      exact OpenBallRVGeometry.rv_sub_constant ho x' y y'
        (by rintro ⟨u,hu,he⟩; exact Set.disjoint_left.mp hDE ((Subtype.ext he).symm ▸ hx') hu)
        ⟨y,hy,rfl⟩ ⟨y',hy',rfl⟩
  exact hFirst.trans hSecond

theorem relation_on_disjoint_image_balls_rectangle
    {D E B C J : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {r t : RV (M := M)} (hR : BalancedFibres.HasBalancedFibres D E R f r t)
    (hBD : B ⊆ D) (hImage : f '' B = J)
    (hJ : Cells.IsOneCell J) (hC : Cells.IsOneCell C) (hDis : Disjoint J C) :
    let Q := R ∩ (B ×ˢ C)
    Q = Cells.first Q ×ˢ Cells.second Q := by
  intro Q
  apply (relation_eq_projection_product_iff Q).mpr
  intro p hp q hq
  have hTagP : rv (p.2-f p.1) = t :=
    (Set.ext_iff.mp (hR.vertical p.1 (hBD hp.2.1)) p.2).mp hp.1
  have hTag : rv (q.2-f p.1) = t := by
    exact (disjoint_one_cells_rv_difference_constant hJ hC hDis
      (hImage ▸ ⟨p.1,hp.2.1,rfl⟩) (hImage ▸ ⟨p.1,hp.2.1,rfl⟩)
      hq.2.2 hp.2.2).trans hTagP
  refine ⟨?_,hp.2.1,hq.2.2⟩
  exact (Set.ext_iff.mp (hR.vertical p.1 (hBD hp.2.1)) q.2).mpr hTag

variable {S : Set M} {m l a b : ℕ}
variable {U : DefSet (M := M) S 1 m} {V : DefSet (M := M) S 1 l}
variable {U' : DefSet (M := M) S 1 a} {V' : DefSet (M := M) S 1 b}

theorem inverse_special_bodies_disjoint (T : SpecialBijection V V') (p q : V')
    (hOld : (T.inverseMap p).val.2 = (T.inverseMap q).val.2)
    (hDifferent : ¬ SameRV p.val q.val) :
    Disjoint (InverseOneCells.typedBody T p) (InverseOneCells.typedBody T q) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u,hu,hup⟩ ⟨v,hv,hvq⟩
  have hUL := unary_inverse_fibre_labels T p u.val ⟨u,rfl,hup⟩
  have hVL := unary_inverse_fibre_labels T q v.val ⟨v,rfl,hvq⟩
  have huv : u = v := by
    apply Subtype.ext
    refine Prod.ext ?_ (hUL.trans (hOld.trans hVL.symm))
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact Subtype.ext (hu.trans hv.symm)
  exact hDifferent (hup.symm.trans (huv ▸ hvq))

theorem prepared_unary_body_image (TU : SpecialBijection U U') (TV : SpecialBijection V V')
    (f : Map U V) (hf : Function.Bijective f)
    (hc : Contractible (unaryConjugate TU TV f))
    (hb : Contractible (Map.inverse (unaryConjugate TU TV f) (unaryConjugate_bijective TU TV f hf)))
    (p : U') (φ : VF (M := M) → VF (M := M))
    (hφ : ∀ u : U, u.val ∈ TU.inverseFibre p → vfAt (f u).val 0 = φ (vfAt u.val 0)) :
    φ '' InverseOneCells.typedBody TU p =
      InverseOneCells.typedBody TV (unaryConjugate TU TV f p) := by
  have hImage := unary_conjugate_inverse_fibre_image TU TV f hf hc hb p
  ext y
  constructor
  · rintro ⟨x,⟨u,hu,hup⟩,rfl⟩
    have hUF : u.val ∈ TU.inverseFibre p := ⟨u,rfl,hup⟩
    have hVF : (f u).val ∈ TV.inverseFibre (unaryConjugate TU TV f p) := by
      rw [← hImage]
      exact ⟨u,hUF,rfl⟩
    obtain ⟨v,hv,hvKey⟩ := hVF
    refine ⟨v,?_,hvKey⟩
    have hx : vfAt u.val 0 = x := Subtype.ext hu
    exact congrArg Subtype.val ((congrArg (fun q : Point (M := M) 1 l => vfAt q 0) hv).trans
      ((hφ u hUF).trans (congrArg φ hx)))
  · rintro ⟨v,hv,hvp⟩
    have hVF : v.val ∈ TV.inverseFibre (unaryConjugate TU TV f p) := ⟨v,rfl,hvp⟩
    rw [← hImage] at hVF
    obtain ⟨u,hu,he⟩ := hVF
    obtain ⟨w,hw,hwp⟩ := hu
    have hwu : w = u := Subtype.ext hw
    refine ⟨vfAt u.val 0,⟨u,rfl,hwu ▸ hwp⟩,?_⟩
    exact (hφ u ⟨u,rfl,hwu ▸ hwp⟩).symm.trans
      (Subtype.ext ((congrArg (fun q : Point (M := M) 1 l => (vfAt q 0).val) he).trans hv))

end IntegrationInACVF.Section7
