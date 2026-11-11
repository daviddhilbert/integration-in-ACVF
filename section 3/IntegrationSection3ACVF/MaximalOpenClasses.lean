import IntegrationSection3ACVF.ThinFamilyGeometry

/-! The intrinsic maximal open balls of a finite disjoint thin family
are exactly its displayed maximal open classes. Open-to-open bijections
preserve this intrinsic maximality. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry

namespace IntegrationInACVF.Section3ACVF.MaximalOpenClasses

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def IsMaximal (A D : Set M) : Prop := PaperBalls.IsOpenBall D ∧ D ⊆ A ∧
  ∀ E, PaperBalls.IsOpenBall E → D ⊆ E → E ⊆ A → E ⊆ D

def OpenToOpen (A : Set M) (f : M → M) : Prop :=
  ∀ D ⊆ A, PaperBalls.IsOpenBall D ↔ PaperBalls.IsOpenBall (f '' D)

theorem class_maximal (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (F : Finset (PuncturedBall M)) (hThin : ∀ d ∈ F, IsThin d)
    (hDis : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (d : PuncturedBall M) (hd : d ∈ F) (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hParent : d.parent = gammaBall a α false)
    (j : BallImaginaries.Ball M) (hj : j ∈ MaximalSubballGeometry.classes d α) :
    IsMaximal (body F) (BallImaginaries.underlying j) := by
  obtain ⟨b,hb⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ hj.1.1 α hj.1.2
  have ho : PaperBalls.IsOpenBall (BallImaginaries.underlying j) := Or.inr ⟨b,α,hb⟩
  have hs : BallImaginaries.underlying j ⊆ body F := fun x hx => ⟨d,hd,hj.2 hx⟩
  refine ⟨ho,hs,?_⟩
  intro E hE hJE hEF
  obtain ⟨e,he,c,β,hParentE,k,hk,hEK⟩ := open_subset_class δ hδ F hThin E hE hEF
  obtain ⟨x,hx⟩ := encodedBall_nonempty (BallCodeGeometry.underlying_isBall j)
  have hxe : x ∈ e.body := hk.2 (hEK (hJE hx))
  have hde : d = e := by
    by_contra hn
    exact (Set.disjoint_left.mp (hDis hd he hn) (hj.2 hx) hxe).elim
  subst e
  have hαβ : α = β := BallRadiusGeometry.gamma_radius_unique δ hδ a c α β false false
    (hParent.symm.trans hParentE)
  subst β
  have hjk : j = k := by
    by_contra hn
    exact (Set.disjoint_left.mp (MaximalSubballGeometry.classes_disjoint δ hδ d α hj hk hn)
      hx (hEK (hJE hx))).elim
  exact fun y hy => (congrArg BallImaginaries.underlying hjk).symm ▸ hEK hy

theorem maximal_is_class (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (F : Finset (PuncturedBall M)) (hThin : ∀ d ∈ F, IsThin d)
    (D : Set M) (hD : IsMaximal (body F) D) :
    ∃ d ∈ F, ∃ a : VFType (M := M), ∃ α : Values.Gamma (M := M),
      d.parent = gammaBall a α false ∧ ∃ j ∈ MaximalSubballGeometry.classes d α,
        D = BallImaginaries.underlying j := by
  obtain ⟨d,hd,a,α,hParent,j,hj,hDj⟩ := open_subset_class δ hδ F hThin D hD.1 hD.2.1
  obtain ⟨b,hb⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ hj.1.1 α hj.1.2
  have ho : PaperBalls.IsOpenBall (BallImaginaries.underlying j) := Or.inr ⟨b,α,hb⟩
  have hs : BallImaginaries.underlying j ⊆ body F := fun x hx => ⟨d,hd,hj.2 hx⟩
  exact ⟨d,hd,a,α,hParent,j,hj,Set.Subset.antisymm hDj (hD.2.2 _ ho hDj hs)⟩

theorem image_maximal {A B D : Set M} (f : M → M) (hbij : Set.BijOn f A B)
    (hoo : OpenToOpen A f) (hD : IsMaximal A D) : IsMaximal B (f '' D) := by
  refine ⟨(hoo D hD.2.1).mp hD.1,?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact hbij.1 (hD.2.1 hx)
  · intro E hE hDE hEB
    let C := A ∩ f ⁻¹' E
    have hCA : C ⊆ A := fun _ hx => hx.1
    have hImage : f '' C = E := by
      apply Set.Subset.antisymm
      · rintro y ⟨x,hx,rfl⟩
        exact hx.2
      · intro y hy
        obtain ⟨x,hx,he⟩ := hbij.2.2 (hEB hy)
        exact ⟨x,⟨hx,show f x ∈ E from he.symm ▸ hy⟩,he⟩
    have hCopen : PaperBalls.IsOpenBall C := (hoo C hCA).mpr (hImage.symm ▸ hE)
    have hDC : D ⊆ C := fun x hx => ⟨hD.2.1 hx,hDE ⟨x,hx,rfl⟩⟩
    have hCD := hD.2.2 C hCopen hDC hCA
    intro y hy
    obtain ⟨x,hx,he⟩ := (Set.ext_iff.mp hImage y).mpr hy
    exact ⟨x,hCD hx,he⟩

end IntegrationInACVF.Section3ACVF.MaximalOpenClasses
