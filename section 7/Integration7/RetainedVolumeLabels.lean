import Integration7.CanonicalLiftVolumePresentations
import IntegrationSection5.RelativeLabelPreservation

/-! An old density label stays nonzero on literal lifts and after
special bijections or focus steps, with no new parameter choices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (SpecialBijection Focus carrier)
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k a b n : ℕ}

theorem lift_density_label_nonzero (U : PositiveRVVolumeObject (M := M) S k)
    {A : SpecialTransformations.Section5.DefSet (M := M) S (k+1) U.underlying.obj.arity}
    (h : Section6.PresentsLift U.underlying.obj A)
    (δ : Fin U.underlying.obj.arity) (hDensity : ∀ u, U.form.value u = u.val δ) (p : A) :
    (p.val.2 δ).val ≠ iRVZero := by
  obtain ⟨u,hu,_⟩ := (h p.val).mp p.property
  have hn := (rv_nonzero_iff_raw (U.form.value u)).mp (U.form.nonzero u)
  have he := (hDensity u).trans (congrFun hu δ)
  exact fun hz => hn ((congrArg Subtype.val he).trans hz)

theorem focus_density_label_nonzero
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {i : Fin n} {j : Fin a} (D : Focus A i j) (δ : Fin a)
    (hDensity : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (q : D.etaImage) :
    (q.val.2 δ).val ≠ iRVZero := by
  obtain ⟨p,hp⟩ := q.property
  have he : q.val.2 = p.val.2 :=
    (congrArg Prod.snd hp).symm.trans (D.toFocusGeometry.eta_labels p.val)
  exact fun hz => hDensity p ((congrArg (fun r => (r δ).val) he).symm.trans hz)

theorem special_density_label_nonzero
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S n b}
    (T : SpecialBijection A B) (δ : Fin a)
    (hDensity : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (q : B) :
    (q.val.2 (Section5.suffixIndex (Section5.special_chain_rvArity_le T.chain) δ)).val ≠ iRVZero := by
  have h := Section5.special_oldLabels T (T.inverseMap q) δ
  rw [T.apply_inverse] at h
  exact fun hz => hDensity (T.inverseMap q) ((congrArg Subtype.val h).symm.trans hz)

end IntegrationInACVF.Section7
