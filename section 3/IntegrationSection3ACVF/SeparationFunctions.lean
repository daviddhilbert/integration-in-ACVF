import IntegrationSection3ACVF.Separation

/-! Function consequences of corrected 3.11. Full partial-domain
graphs are used in both directions. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.SeparationFunctions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem open_nonempty {O : Set M} (hOpen : PaperBalls.IsOpenBall O) : O.Nonempty := by
  rcases hOpen with hVF | ⟨a,α,he⟩
  · exact ⟨(0 : VFType (M := M)).val,hVF.symm ▸ (0 : VFType (M := M)).property⟩
  · exact ⟨a.val,he.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem a α true⟩

theorem closed_nonempty {L : Set M} (hClosed : PaperBalls.IsClosedBall L) : L.Nonempty := by
  rcases hClosed with hVF | ⟨a,ha⟩ | ⟨a,α,ha⟩
  · exact ⟨(0 : VFType (M := M)).val,hVF.symm ▸ (0 : VFType (M := M)).property⟩
  · exact ⟨a.val,ha.symm ▸ Set.mem_singleton a.val⟩
  · exact ⟨a.val,ha.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem a α false⟩

theorem punctured_nonempty (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedBall M) : d.body.Nonempty := by
  obtain ⟨x,hx,havoid⟩ := CanonicalBallSupport.encoded_avoids_finite_proper_subballs δ hδ
    d.parent d.parent_ball d.holes (fun h hh => ⟨d.holes_ball h hh,d.holes_proper h hh⟩)
  exact ⟨x,hx,fun ⟨h,hh,hxh⟩ => havoid h hh hxh⟩

theorem open_infinite (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {O : Set M} (hOpen : PaperBalls.IsOpenBall O) : O.Infinite := by
  rcases hOpen with hVF | ⟨a,α,he⟩
  · apply (InfiniteOrdinaryBalls.open_infinite h00 δ hδ (0 : VFType (M := M)) 1).mono
    intro x hx
    rw [hVF]
    exact hx.1
  · rw [he]
    exact InfiniteOrdinaryBalls.open_infinite h00 δ hδ a α

theorem no_function_from_open (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {O L : Set M} (hOpen : PaperBalls.IsOpenBall O)
    (hO : AdjoinBall.AtomicOver B O) (hL : AdjoinBall.AtomicOver B L)
    (hTarget : (PaperBalls.IsClosedBall L ∧
      ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius L r ∧
        r < (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M))) ∨
      ∃ d : PuncturedBall M, PaperBalls.IsThinAnnulus d ∧ d.body = L)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn O f))
    (hfL : ∀ x ∈ O, f x ∈ L) : False := by
  let R : Set (M × M) := {p | p.1 ∈ O ∧ p.2 = f p.1}
  have hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R} := hf
  have hsub : R ⊆ O ×ˢ L := fun p hp => ⟨hp.1,hp.2.symm ▸ hfL p.1 hp.1⟩
  obtain ⟨x,hx⟩ := open_nonempty hOpen
  have hne : R.Nonempty := ⟨(x,f x),hx,rfl⟩
  have hfin (x : M) (_ : x ∈ O) : {y | (x,y) ∈ R}.Finite :=
    (Set.finite_singleton (f x)).subset (fun y hy => hy.2)
  exact Separation.lemma_3_11 B h00 δ hδ hδ1 hOpen hO hL hTarget hR hsub hne hfin

theorem no_finite_to_one_to_open (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {O L : Set M} (hOpen : PaperBalls.IsOpenBall O)
    (hO : AdjoinBall.AtomicOver B O) (hL : AdjoinBall.AtomicOver B L)
    (hTarget : PaperBalls.IsClosedBall L ∨
      ∃ d : PuncturedBall M, PaperBalls.IsThinAnnulus d ∧ d.body = L)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn L f))
    (hfO : ∀ y ∈ L, f y ∈ O)
    (hfinite : ∀ x ∈ O, {y | y ∈ L ∧ f y = x}.Finite) : False := by
  let R : Set (M × M) := {p | p.2 ∈ L ∧ p.1 = f p.2}
  have hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R} :=
    hf.preimage_comp (![1,0] : Fin 2 → Fin 2)
  have hsub : R ⊆ O ×ˢ L := fun p hp => ⟨hp.2.symm ▸ hfO p.2 hp.1,hp.1⟩
  have hLne : L.Nonempty := by
    rcases hTarget with hc | ⟨d,_,he⟩
    · exact closed_nonempty hc
    · rw [← he]
      exact punctured_nonempty δ hδ1 d
  obtain ⟨y,hy⟩ := hLne
  have hne : R.Nonempty := ⟨(f y,y),hy,rfl⟩
  have hfin (x : M) (hx : x ∈ O) : {y | (x,y) ∈ R}.Finite := by
    convert hfinite x hx using 1
    ext y
    exact and_congr_right (fun _ => eq_comm)
  have hsep (ht : (PaperBalls.IsClosedBall L ∧
      ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius L r ∧
        r < (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M))) ∨
      ∃ d : PuncturedBall M, PaperBalls.IsThinAnnulus d ∧ d.body = L) : False :=
    Separation.lemma_3_11 B h00 δ hδ hδ1 hOpen hO hL ht hR hsub hne hfin
  rcases hTarget with hc | hthin
  · rcases hc with hVF | ⟨a,ha⟩ | ⟨b,α,hb⟩
    · exact OpenBallConstancy.atomic_not_contains_vf B hL (hVF.symm ▸ Set.Subset.rfl)
    · have hproj : ∀ x ∈ O, ∃ y ∈ L, (x,y) ∈ R := by
        let p := @ParameterPresentation.presentation M sM hM
        letI := CanonicalStructure.normalize (M := M)
        exact (RelationProjections.surjective hO.2 hL.2 hR hsub hne).1
      apply open_infinite h00 δ hδ1 hOpen
      apply (Set.finite_singleton (f a.val)).subset
      intro x hx
      obtain ⟨y,hy,hxy⟩ := hproj x hx
      have hya : y = a.val := by rwa [ha] at hy
      exact hya ▸ hxy.2
    · have hαinf : α.val < Values.infinity :=
        lt_of_le_of_ne (Values.le_infinity α.val) α.property
      exact hsep (Or.inl ⟨Or.inr (Or.inr ⟨b,α,hb⟩),↑α.val,
        Or.inr (Or.inr ⟨b,α,false,hb,rfl⟩),WithBot.coe_lt_coe.mpr hαinf⟩)
  · exact hsep (Or.inr hthin)

end IntegrationInACVF.Section3ACVF.SeparationFunctions
