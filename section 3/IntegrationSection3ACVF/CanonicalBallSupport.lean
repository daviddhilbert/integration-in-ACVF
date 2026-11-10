import IntegrationSection3ACVF.GammaCosetGeometry
import IntegrationSection3.MinimalBallSupport

/-! Canonical finite supports in the actual ACVF ball family.
Reuses the pinned ACVF-QE proof of Johnson's Lemma 2.3.7 rather than
assuming the finite proper-subball non-covering property. The extra raw
universe is a logical top element; it never occurs in a minimal support. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open ValOneEC
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.MinimalBallSupport

namespace IntegrationInACVF.Section3ACVF.CanonicalBallSupport

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def ballFamily : Set (Set M) := {b | IsBall b} ∪ {Set.univ}

theorem encodedBall_nonempty {B : Set M} (hB : IsBall B) : B.Nonempty := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨a,r,he | he⟩ := encodedBall_disc v hv B hB
  · exact ⟨a.val,(Set.ext_iff.mp he a).mpr (Balls.centre_mem_openDisc v a r)⟩
  · exact ⟨a.val,(Set.ext_iff.mp he a).mpr (Balls.centre_mem_closedDisc v a r)⟩

theorem encodedBall_isValBall {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {B : Set M} (hB : IsBall B) :
    Johnson.IsValBall v {x : VFType (M := M) | x.val ∈ B} := by
  have hbridge (C : Set (VFType (M := M)))
      (h : IsKBall (RingHom.id (VFType (M := M))) v C) : Johnson.IsValBall v C := by
    cases h with
    | closed a r => exact Johnson.IsValBall.closed a r
    | openball a r => exact Johnson.IsValBall.openball a r
    | univ => exact Johnson.IsValBall.univ
  exact hbridge _ (encodedBall_isKBall v hv B hB)

theorem valuation_nontrivial {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) : ∃ x : VFType (M := M), 1 < v x := by
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative δ
  have hr0 : r ≠ 0 := by
    intro he
    have hz : Values.vfValueHom r = Values.infinity := by
      rw [he,map_zero]
      exact Values.infinity_eq_zero.symm
    exact δ.property (hr.symm.trans hz)
  have hlt : v r < 1 := by
    apply lt_of_not_ge
    intro he
    have hp := (Values.vf_pred_iff_gamma_le (1 : VFType (M := M)) r).mp
      ((hv 1 r).mpr (by simpa only [map_one] using he))
    rw [hr,map_one] at hp
    have hd : δ ≤ 1 := by
      change δ.val ≤ (1 : Values.Gamma (M := M)).val
      rw [Values.gamma_val_one]
      exact hp
    exact not_le_of_gt hδ hd
  exact (Johnson.exists_ne_zero_val_lt_one_iff v).mp ⟨r,hr0,hlt⟩

theorem encoded_avoids_finite_proper_subballs (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    AvoidsFiniteProperSubballs {b : Set M | IsBall b} := by
  classical
  intro b hb F hF
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  let C : Set M → Set (VFType (M := M)) := fun c => {x | x.val ∈ c}
  obtain ⟨a,ha⟩ := encodedBall_nonempty hb
  have hne : (C b).Nonempty := ⟨⟨a,isBall_subset_vf b hb ha⟩,ha⟩
  have hnot := Johnson.ne_finite_union_of_proper_subballs v (valuation_nontrivial v hv δ hδ)
    (encodedBall_isValBall v hv hb) hne F C
    (fun c hc => encodedBall_isValBall v hv (hF c hc).1)
    (fun c hc x hx => (hF c hc).2.1 hx)
    (by
      intro c hc he
      apply (hF c hc).2.2
      intro x hx
      exact (Set.ext_iff.mp he (⟨x,isBall_subset_vf b hb hx⟩ : VFType (M := M))).mpr hx)
  by_contra hn
  have hcover : C b = ⋃ c ∈ F, C c := by
    ext x
    constructor
    · intro hx
      have hh : ∃ c ∈ F, x.val ∈ c := by
        by_contra hh
        exact hn ⟨x.val,hx,fun c hc hxc => hh ⟨c,hc,hxc⟩⟩
      obtain ⟨c,hc,hxc⟩ := hh
      exact Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨hc,hxc⟩⟩
    · intro hx
      obtain ⟨c,hc,hxc⟩ : ∃ c ∈ F, x.val ∈ c := by
        simpa only [Set.mem_iUnion,C,Set.mem_ofPred_eq,exists_prop] using hx
      exact (hF c hc).2.1 hxc
  exact hnot hcover

theorem ballFamily_laminar : IsLaminar (ballFamily (M := M)) := by
  intro b hb c hc
  rcases hb with hb | hb
  · rcases hc with hc | hc
    · exact encodedBalls_laminar b hb c hc
    · have he : c = Set.univ := hc
      exact Or.inl (he.symm ▸ Set.subset_univ _)
  · have he : b = Set.univ := hb
    exact Or.inr (Or.inl (he.symm ▸ Set.subset_univ _))

theorem ballFamily_avoids (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    AvoidsFiniteProperSubballs (ballFamily (M := M)) := by
  classical
  intro b hb F hF
  have hballs : ∀ c ∈ F, IsBall c := by
    intro c hc
    rcases (hF c hc).1 with h | h
    · exact h
    · have he : c = Set.univ := h
      exact ((hF c hc).2.2 (he.symm ▸ Set.subset_univ _)).elim
  rcases hb with hb | hb
  · exact encoded_avoids_finite_proper_subballs δ hδ b hb F
      (fun c hc => ⟨hballs c hc,(hF c hc).2⟩)
  · have he : b = Set.univ := hb
    refine ⟨iRVZero,he.symm ▸ Set.mem_univ _,?_⟩
    intro c hc hx
    have hVF := isBall_subset_vf c (hballs c hc) hx
    have hsort : SortTag.vf = SortTag.rv :=
      CanonicalStructure.sort_unique hM hVF (rv_zero_mem hM)
    cases hsort

theorem minimal_support_encoded {F : Finset (Set M)} {A : Set M}
    (hF : IsMinimalSupport (ballFamily (M := M)) F A) : ∀ b ∈ F, IsBall b := by
  intro b hb
  rcases hF.1.1 b hb with h | h
  · exact h
  · exact (essential_ne_univ hF hb h).elim

/-- The unique minimal support is an intrinsic finite family of actual
balls. This is the existence/uniqueness step; its original-base definability
is to be recovered from the minimal-support formula. -/
theorem exists_unique_minimal_support (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (A : Set M)
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAVF : A ⊆ {x | iVF x}) : ∃! F, IsMinimalSupport (ballFamily (M := M)) F A := by
  have hcm (Q : Set M) := normalized_cMinimalOn (M := M) Q
  have hs : HasFiniteBallSupport {b : Set M | IsBall b} A := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.finite_ball_support hcm hA hAVF
  have hs' := hs.mono (show {b : Set M | IsBall b} ⊆ ballFamily from fun _ h => Or.inl h)
  obtain ⟨F,hF⟩ := exists_minimal_support hs'
  refine ⟨F,hF,fun G hG => ?_⟩
  exact minimal_unique ballFamily_laminar (Or.inr rfl) (ballFamily_avoids δ hδ) hG hF

end IntegrationInACVF.Section3ACVF.CanonicalBallSupport
