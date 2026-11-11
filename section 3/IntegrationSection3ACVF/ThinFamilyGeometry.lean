import IntegrationSection3ACVF.ResiduePunctures

/-! Open balls contained in a finite union of thin punctured balls lie in
one of the displayed maximal open classes. Inactive containing parents
are removed before applying finite proper-subball non-covering. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.ThinFamilyGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def IsThin (d : PuncturedBall M) : Prop :=
  ∃ a : VFType (M := M), ∃ α : Values.Gamma (M := M),
    d.parent = gammaBall a α false ∧
      ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true

def body (F : Finset (PuncturedBall M)) : Set M := {x | ∃ d ∈ F, x ∈ d.body}

theorem covered_ball_parent (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (F : Finset (PuncturedBall M)) (D : Set M) (hD : IsBall D) (hsub : D ⊆ body F) :
    ∃ d ∈ F, (d.body ∩ D).Nonempty ∧ D ⊆ d.parent := by
  classical
  by_contra hn
  let G := F.filter (fun d => (d.body ∩ D).Nonempty)
  have hproper (d : PuncturedBall M) (hd : d ∈ G) : d.parent ⊂ D := by
    obtain ⟨hdF,hm⟩ := Finset.mem_filter.mp hd
    have hnot : ¬ D ⊆ d.parent := fun hs => hn ⟨d,hdF,hm,hs⟩
    rcases encodedBalls_laminar d.parent d.parent_ball D hD with hp | hp | hdis
    · exact Set.ssubset_iff_subset_ne.mpr ⟨hp,fun he => hnot (he ▸ Set.Subset.rfl)⟩
    · exact (hnot hp).elim
    · obtain ⟨x,hxd,hxD⟩ := hm
      exact (Set.disjoint_left.mp hdis hxd.1 hxD).elim
  let H := G.image PuncturedBall.parent
  have hH : ∀ B ∈ H, IsBall B ∧ B ⊂ D := by
    intro B hB
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hB
    exact ⟨d.parent_ball,hproper d hd⟩
  obtain ⟨x,hx,havoid⟩ := encoded_avoids_finite_proper_subballs δ hδ D hD H hH
  obtain ⟨d,hd,hxd⟩ := hsub hx
  have hdG : d ∈ G := Finset.mem_filter.mpr ⟨hd,⟨x,hxd,hx⟩⟩
  exact havoid d.parent (Finset.mem_image.mpr ⟨d,hdG,rfl⟩) hxd.1

theorem open_subset_class (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (F : Finset (PuncturedBall M)) (hThin : ∀ d ∈ F, IsThin d)
    (D : Set M) (hOpen : PaperBalls.IsOpenBall D) (hsub : D ⊆ body F) :
    ∃ d ∈ F, ∃ a : VFType (M := M), ∃ α : Values.Gamma (M := M),
      d.parent = gammaBall a α false ∧
        ∃ j ∈ MaximalSubballGeometry.classes d α, D ⊆ BallImaginaries.underlying j := by
  have hD : IsBall D := by
    rcases hOpen with hvf | ⟨a,α,rfl⟩
    · exact Or.inl hvf
    · exact BallEnlargementGeometry.gammaBall_isBall a α true
  obtain ⟨d,hd,hMeet,hParent⟩ := covered_ball_parent δ hδ F D hD hsub
  obtain ⟨a,α,ha,hholes⟩ := hThin d hd
  have hNe : D ≠ d.parent := by
    intro he
    have hBoth := BallRadiusGeometry.open_closed_only_vf δ hδ hOpen
      (show PaperBalls.IsClosedBall D from Or.inr (Or.inr ⟨a,α,he.trans ha⟩))
    exact BallRadiusGeometry.gammaBall_ne_vf δ hδ a α false ((he.trans ha).symm.trans hBoth)
  have hProper : D ⊂ gammaBall a α false := by
    rw [← ha]
    exact Set.ssubset_iff_subset_ne.mpr ⟨hParent,hNe⟩
  obtain ⟨b,hb⟩ := MaximalSubballGeometry.proper_ball_in_maximal δ hδ a α hD hProper
  obtain ⟨x,hxd,hxD⟩ := hMeet
  let u : VFType (M := M) := ⟨x,d.body_subset_vf hxd⟩
  have hBody := MaximalSubballGeometry.class_subset_body d α a ha hholes b u hxd (hb hxD)
  obtain ⟨j,hj⟩ := GammaCosetGeometry.gammaBall_coded b α
  refine ⟨d,hd,a,α,ha,j,⟨⟨Or.inr ⟨b,α,hj⟩,
    Or.inr (Or.inr ⟨b,α,true,hj,rfl⟩)⟩,?_⟩,?_⟩
  · rwa [hj]
  · rwa [hj]

end IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
