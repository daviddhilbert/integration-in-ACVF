import IntegrationSection3ACVF.AffineHoleGeometry
import IntegrationSection3ACVF.PuncturedGeometry

/-! Actual geometry of maximal open classes of a closed ordinary
parent with finitely many maximal open holes. No residue-field structure
or transitivity result is assumed. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.PuncturedGeometry

namespace IntegrationInACVF.Section3ACVF.MaximalSubballGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def classes (d : PuncturedBall M) (α : Values.Gamma (M := M)) : Set (BallImaginaries.Ball M) :=
  {j | j ∈ AffineHoleGeometry.radiusClass α ∧ BallImaginaries.underlying j ⊆ d.body}

theorem equal_of_inter (a b : VFType (M := M)) (α : Values.Gamma (M := M)) (strict : Bool)
    (hmeet : (gammaBall a α strict ∩ gammaBall b α strict).Nonempty) :
    gammaBall a α strict = gammaBall b α strict := by
  rcases encodedBalls_laminar _ (BallEnlargementGeometry.gammaBall_isBall a α strict)
    _ (BallEnlargementGeometry.gammaBall_isBall b α strict) with hab | hba | hd
  · exact BallEnlargementGeometry.gamma_same_kind_eq_of_subset a b α strict hab
  · exact (BallEnlargementGeometry.gamma_same_kind_eq_of_subset b a α strict hba).symm
  · obtain ⟨x,hxa,hxb⟩ := hmeet
    exact (Set.disjoint_left.mp hd hxa hxb).elim

theorem proper_ball_in_maximal (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (c : VFType (M := M)) (α : Values.Gamma (M := M)) {D : Set M} (hD : IsBall D)
    (hproper : D ⊂ gammaBall c α false) :
    ∃ a : VFType (M := M), D ⊆ gammaBall a α true := by
  obtain ⟨r,hr⟩ := PaperBallInvariants.hasRadius_exists hD
  rcases hr with ⟨hVF,_⟩ | ⟨a,ha,_⟩ | ⟨a,β,strict,ha,_⟩
  · exact (hproper.2 (by rw [hVF]; exact fun _ hx => hx.choose)).elim
  · refine ⟨a,?_⟩
    rw [ha]
    exact Set.singleton_subset_iff.mpr (BallEnlargementGeometry.gammaBall_centre_mem a α true)
  · have hsub : gammaBall a β strict ⊂ gammaBall c α false := by rwa [ha] at hproper
    have hαβ := BallEnlargementGeometry.gamma_radius_le_of_subset δ hδ a c α β strict false hsub.1
    by_cases he : α = β
    · have hsame : gammaBall a α strict ⊂ gammaBall c α false := by rwa [← he] at hsub
      have hkind := BallEnlargementGeometry.proper_same_radius_kinds a c α strict false hsame
      refine ⟨a,?_⟩
      simpa only [ha,← he,hkind.1] using
        (Set.Subset.rfl : gammaBall a α true ⊆ gammaBall a α true)
    · have hlt : α < β := lt_of_le_of_ne hαβ he
      have hc := BallEnlargementGeometry.closed_inside_parent δ hδ a a α β hlt true
        (BallEnlargementGeometry.gammaBall_centre_mem a α true)
      refine ⟨a,?_⟩
      rw [ha]
      intro x hx
      apply hc.1
      obtain ⟨hxVF,hxval,_⟩ := hx
      exact ⟨hxVF,hxval,fun he => (Bool.false_ne_true he).elim⟩

theorem class_subset_body (d : PuncturedBall M) (α : Values.Gamma (M := M))
    (c : VFType (M := M)) (hd : d.parent = gammaBall c α false)
    (hholes : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true)
    (a x : VFType (M := M)) (hx : x.val ∈ d.body) (hxa : x.val ∈ gammaBall a α true) :
    gammaBall a α true ⊆ d.body := by
  have he := equal_of_inter a x α true
    ⟨x.val,hxa,BallEnlargementGeometry.gammaBall_centre_mem x α true⟩
  have hxParent : x.val ∈ gammaBall c α false := hd ▸ hx.1
  have hsub : gammaBall a α true ⊆ d.parent := by
    rw [he,hd]
    exact (BallEnlargementGeometry.open_inside_closed_same_radius x c α hxParent).1
  intro y hy
  refine ⟨hsub hy,?_⟩
  rintro ⟨h,hh,hyh⟩
  obtain ⟨b,hb⟩ := hholes h hh
  have heh := equal_of_inter a b α true ⟨y,hy,hb ▸ hyh⟩
  have hxh : x.val ∈ h := by
    rw [hb,← heh]
    exact hxa
  exact hx.2 ⟨h,hh,hxh⟩

theorem covers_body (d : PuncturedBall M) (α : Values.Gamma (M := M))
    (c : VFType (M := M)) (hd : d.parent = gammaBall c α false)
    (hholes : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true) :
    ∀ x ∈ d.body, ∃ j ∈ classes d α, x ∈ BallImaginaries.underlying j := by
  intro x hx
  let a : VFType (M := M) := ⟨x,d.body_subset_vf hx⟩
  obtain ⟨j,hj⟩ := GammaCosetGeometry.gammaBall_coded a α
  have ha : a.val ∈ gammaBall a α true := BallEnlargementGeometry.gammaBall_centre_mem a α true
  refine ⟨j,⟨⟨Or.inr ⟨a,α,hj⟩,Or.inr (Or.inr ⟨a,α,true,hj,rfl⟩)⟩,?_⟩,?_⟩
  · rw [hj]
    exact class_subset_body d α c hd hholes a a hx ha
  · rwa [hj]

theorem classes_disjoint (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedBall M) (α : Values.Gamma (M := M)) :
    (classes d α).Pairwise fun j k => Disjoint (BallImaginaries.underlying j) (BallImaginaries.underlying k) := by
  intro j hj k hk hjk
  obtain ⟨a,ha⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ hj.1.1 α hj.1.2
  obtain ⟨b,hb⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ hk.1.1 α hk.1.2
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  have he := equal_of_inter a b α true ⟨x,ha ▸ hxj,hb ▸ hxk⟩
  exact hjk (BallImaginaries.underlying_injective (ha.trans (he.trans hb.symm)))

theorem class_proper_parent (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedBall M) (α : Values.Gamma (M := M))
    (c : VFType (M := M)) (hd : d.parent = gammaBall c α false)
    (j : BallImaginaries.Ball M) (hj : j ∈ classes d α) :
    BallImaginaries.underlying j ⊂ d.parent := by
  obtain ⟨a,ha⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ hj.1.1 α hj.1.2
  have ham : a.val ∈ BallImaginaries.underlying j :=
    ha.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem a α true
  have hac : a.val ∈ gammaBall c α false := hd ▸ (hj.2 ham).1
  rw [ha,hd]
  exact BallEnlargementGeometry.open_inside_closed_same_radius a c α hac

theorem classes_infinite (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedBall M) (α : Values.Gamma (M := M))
    (c : VFType (M := M)) (hd : d.parent = gammaBall c α false)
    (hholes : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true) :
    (classes d α).Infinite := by
  classical
  intro hfinite
  let G := d.holes ∪ hfinite.toFinset.image (BallImaginaries.underlying (M := M))
  have hG : ∀ b ∈ G, IsBall b ∧ b ⊂ d.parent := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact ⟨d.holes_ball b hb,d.holes_proper b hb⟩
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
      exact ⟨BallCodeGeometry.underlying_isBall j,
        class_proper_parent δ hδ d α c hd j (hfinite.mem_toFinset.mp hj)⟩
  obtain ⟨x,hx,havoid⟩ := encoded_avoids_finite_proper_subballs δ hδ d.parent d.parent_ball G hG
  have hxBody : x ∈ d.body := ⟨hx,fun ⟨b,hb,hxb⟩ =>
    havoid b (Finset.mem_union_left _ hb) hxb⟩
  obtain ⟨j,hj,hxj⟩ := covers_body d α c hd hholes x hxBody
  exact havoid _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨j,hfinite.mem_toFinset.mpr hj,rfl⟩)) hxj

theorem test_ball (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedBall M) (α : Values.Gamma (M := M))
    (c : VFType (M := M)) (hd : d.parent = gammaBall c α false)
    (hholes : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true)
    (B : Set M) (hB : IsBall B) :
    d.body ⊆ B ∨ Disjoint d.body B ∨
      ∃ j ∈ classes d α, B ∩ d.body ⊆ BallImaginaries.underlying j := by
  classical
  by_cases hdis : Disjoint d.body B
  · exact Or.inr (Or.inl hdis)
  obtain ⟨x,hxBody,hxB⟩ := Set.not_disjoint_iff.mp hdis
  rcases encodedBalls_laminar B hB d.parent d.parent_ball with hBP | hPB | hdisBP
  · by_cases he : B = d.parent
    · exact Or.inl (he.symm ▸ d.body_subset_parent)
    · have hproper : B ⊂ gammaBall c α false := by
        rw [← hd]
        exact Set.ssubset_iff_subset_ne.mpr ⟨hBP,he⟩
      obtain ⟨a,ha⟩ := proper_ball_in_maximal δ hδ c α hB hproper
      obtain ⟨j,hj⟩ := GammaCosetGeometry.gammaBall_coded a α
      let u : VFType (M := M) := ⟨x,d.body_subset_vf hxBody⟩
      have hsubset := class_subset_body d α c hd hholes a u hxBody (ha hxB)
      refine Or.inr (Or.inr ⟨j,⟨⟨Or.inr ⟨a,α,hj⟩,
        Or.inr (Or.inr ⟨a,α,true,hj,rfl⟩)⟩,?_⟩,?_⟩)
      · rwa [hj]
      · intro y hy
        rw [hj]
        exact ha hy.1
  · exact Or.inl (d.body_subset_parent.trans hPB)
  · exact (Set.disjoint_left.mp hdisBP hxB hxBody.1).elim

end IntegrationInACVF.Section3ACVF.MaximalSubballGeometry
