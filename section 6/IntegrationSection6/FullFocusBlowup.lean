import IntegrationSection6.FocusKeys
import IntegrationSection6.Blowups

/-! Lemma6.9 on the actual full canonical key image. Its definability is
obtained from the proved image calculation, so the original raw RV
presentation and its off-sort interpretation are preserved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
variable {U : RVObject (M := M) S n}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
variable (h : PresentsLift U A) {i : Fin n} {k : Fin U.arity}
variable (D : Focus A i k) (hfull : carrier A ⊆ D.locus)
variable (hnz : ∀ u : U.domain, U.value u i ≠ 0)

/-- The domain is literally the entire canonical RV image after the focus. -/
def fullFocusKeyDomain : DefSet (SpecialTransformations.Section4.rawRVSpace (M := M) (n+U.arity)) S where
  carrier := focusKeyImage D
  definable := by
    rw [focusKeyImage_eq_elementary h D hfull hnz]
    exact (elementaryKeyObject U i).domain.definable

/-- The paper's U_(can o eta): project its first n new RV labels. -/
def fullFocusObject : RVObject (M := M) S n where
  arity := n+U.arity
  domain := fullFocusKeyDomain h D hfull hnz
  volume := selectRVTuple (Fin.castAdd U.arity) (fullFocusKeyDomain h D hfull hnz)

/-- The identity on the actual image gives its elementary-key presentation. -/
def fullFocusObjectKeyIso : fullFocusObject h D hfull hnz ≅ elementaryKeyObject U i :=
  rvIsoOfCarrierEq _ _ _ _ (focusKeyImage_eq_elementary h D hfull hnz) (fun _ => rfl)

include h hnz in
theorem PresentsLift.field_nonzero (p : A) : vfAt p.val i ≠ 0 := by
  obtain ⟨u,_,hv⟩ := (h p.val).mp p.property
  intro he
  apply hnz u
  exact (congrFun hv i).trans ((congrArg rv he).trans RVOperations.rv_zero)

/-- Lemma6.9, with the normalized paper convention excluding an active
zero coordinate. No blowup or RV-image isomorphism is a hypothesis. -/
def lemma_6_9 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    ElementaryBlowup U (fullFocusObject h D hfull hnz) where
  coordinate := i
  admissible := admissible_of_fullFocus hκ hs hsmall h D hfull
    (fun p hp => PresentsLift.field_nonzero h hnz ⟨p,hp⟩)
  iso := (fullFocusObjectKeyIso h D hfull hnz).trans
    (elementaryKeyIso U i (admissible_of_fullFocus hκ hs hsmall h D hfull
      (fun p hp => PresentsLift.field_nonzero h hnz ⟨p,hp⟩))).symm

end IntegrationInACVF.Section6
