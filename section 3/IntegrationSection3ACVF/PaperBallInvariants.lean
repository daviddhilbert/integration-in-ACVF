import IntegrationSection3ACVF.BallRadiusGeometry
import IntegrationSection3ACVF.ValuativeCentreGeometry

/-! The actual radius and valuative-centre predicates are single-valued
on balls, including the singleton and whole-field radius conventions. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.BallRadiusGeometry

namespace IntegrationInACVF.Section3ACVF.PaperBallInvariants

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem singleton_ne_vf (a : VFType (M := M)) : {a.val} ≠ {x | iVF x} := by
  intro he
  have h0 : (0 : VFType (M := M)).val = a.val :=
    (Set.ext_iff.mp he _).mpr (0 : VFType (M := M)).property
  have h1 : (1 : VFType (M := M)).val = a.val :=
    (Set.ext_iff.mp he _).mpr (1 : VFType (M := M)).property
  exact (zero_ne_one : (0 : VFType (M := M)) ≠ 1) (Subtype.ext (h0.trans h1.symm))

theorem hasRadius_exists {D : Set M} (hD : IsBall D) :
    ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius D r := by
  obtain ⟨i,hi⟩ := BallCodeGeometry.encodedBall_coded D hD
  obtain ⟨c,hc⟩ := BallPresentation.decode_surjective i
  have he := BallPresentation.underlying_decode c
  rw [hc,hi] at he
  by_cases h3 : c.val 3 = iVFZero
  · have hclosed : PaperBalls.IsClosedBall D := by
      rw [he,if_pos h3]
      exact BallKindGeometry.closed_raw_isClosedBall
        ⟨BallPresentation.closedTuple c.val,(c.property.resolve_right (fun hn => hn.1 h3)).2⟩
    rcases hclosed with hVF | ⟨a,ha⟩ | ⟨a,γ,ha⟩
    · exact ⟨⊥,Or.inl ⟨hVF,rfl⟩⟩
    · exact ⟨↑Values.infinity,Or.inr (Or.inl ⟨a,ha,rfl⟩)⟩
    · exact ⟨↑γ.val,Or.inr (Or.inr ⟨a,γ,false,ha,rfl⟩)⟩
  · have hopen : PaperBalls.IsOpenBall D := by
      rw [he,if_neg h3]
      exact BallKindGeometry.open_raw_isOpenBall
        ⟨BallPresentation.openTuple c.val,(c.property.resolve_left (fun hz => h3 hz.1)).2⟩
    rcases hopen with hVF | ⟨a,γ,ha⟩
    · exact ⟨⊥,Or.inl ⟨hVF,rfl⟩⟩
    · exact ⟨↑γ.val,Or.inr (Or.inr ⟨a,γ,true,ha,rfl⟩)⟩

theorem hasRadius_unique (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {D : Set M} {r s : PaperBalls.Radius (M := M)}
    (hr : PaperBalls.HasRadius D r) (hs : PaperBalls.HasRadius D s) : r = s := by
  rcases hr with ⟨hDr,rfl⟩ | ⟨a,hDa,rfl⟩ | ⟨a,α,strict,hDa,rfl⟩
  · rcases hs with ⟨_,rfl⟩ | ⟨b,hDb,rfl⟩ | ⟨b,β,other,hDb,rfl⟩
    · rfl
    · exact (singleton_ne_vf b (hDb.symm.trans hDr)).elim
    · exact (gammaBall_ne_vf δ hδ b β other (hDb.symm.trans hDr)).elim
  · rcases hs with ⟨hDs,rfl⟩ | ⟨b,_,rfl⟩ | ⟨b,β,other,hDb,rfl⟩
    · exact (singleton_ne_vf a (hDa.symm.trans hDs)).elim
    · rfl
    · have he := hDb.symm.trans hDa
      cases other with
      | false => exact (gamma_closed_ne_singleton b a β he).elim
      | true => exact (gamma_open_not_closed δ hδ b β (Or.inr (Or.inl ⟨a,he⟩))).elim
  · rcases hs with ⟨hDs,rfl⟩ | ⟨b,hDb,rfl⟩ | ⟨b,β,other,hDb,rfl⟩
    · exact (gammaBall_ne_vf δ hδ a α strict (hDa.symm.trans hDs)).elim
    · have he := hDa.symm.trans hDb
      cases strict with
      | false => exact (gamma_closed_ne_singleton a b α he).elim
      | true => exact (gamma_open_not_closed δ hδ a α (Or.inr (Or.inl ⟨b,he⟩))).elim
    · have hab := gamma_radius_unique δ hδ a b α β strict other (hDa.symm.trans hDb)
      exact congrArg (fun γ : Values.Gamma (M := M) => (↑γ.val : PaperBalls.Radius (M := M))) hab

end IntegrationInACVF.Section3ACVF.PaperBallInvariants
