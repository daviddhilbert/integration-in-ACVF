import IntegrationSection5.ConstantCoordinateFibres
import IntegrationSection5.RVAttachment
import IntegrationSection5.RVCodePredicates
import IntegrationSection5.FiniteMixedFamilyCoding

/-! The all-constant tag locus is original-Gamma definable. After retaining
its RV code as labels, every active VF fibre is finite. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {p m u w d : ℕ}
variable {D : Set (Point (M := M) (p+1) m)}

def allConstantDomain (Q : GammaRVMap G D d) (j : Fin u → Fin d) :
    Set (Point (M := M) (p+1) m) :=
  rvCodeEqualizer (selectRVCode Q j) (GammaRVMap.zero G D Q.domain_definable u)

theorem allConstantDomain_definable (Q : GammaRVMap G D d) (j : Fin u → Fin d) :
    GammaSetDefinable G (allConstantDomain Q j) := rvCodeEqualizer_definable _ _

theorem allConstantDomain_subset (Q : GammaRVMap G D d) (j : Fin u → Fin d) :
    allConstantDomain Q j ⊆ D := by
  rintro a ⟨b,hb,_⟩
  exact hb ▸ b.property

theorem mem_allConstantDomain (Q : GammaRVMap G D d) (j : Fin u → Fin d) (a : D) :
    a.val ∈ allConstantDomain Q j ↔ ∀ i, Q.toFun a (j i) = rv (0 : VF (M := M)) := by
  constructor
  · rintro ⟨b,hb,he⟩
    have hba : b = a := Subtype.ext hb
    subst b
    intro i
    exact congrFun he i
  · intro h
    exact ⟨a,rfl,funext h⟩

def allConstantCode (Q : GammaRVMap G D d) (j : Fin u → Fin d) :
    GammaRVMap G (allConstantDomain Q j) d :=
  Q.restrict _ (allConstantDomain_subset Q j) (allConstantDomain_definable Q j)

def allConstantAttachment (Q : GammaRVMap G D d) (j : Fin u → Fin d) :
    Set (Point (M := M) (p+1) (m+d)) := RVAttachment.target (allConstantCode Q j)

theorem allConstantAttachment_definable (Q : GammaRVMap G D d) (j : Fin u → Fin d) :
    GammaSetDefinable G (allConstantAttachment Q j) := RVAttachment.target_definable _

variable {S : Set M} {A : DefSet (M := M) S (p+1) m} {B : DefSet (M := M) S u w}

theorem allConstantAttachment_family_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (f : Map A B) (hbij : Function.Bijective f) (hf : GammaGraphDefinable G (pointMapGraph f))
    (Q : GammaRVMap G (carrier A) d) (j : Fin u → Fin d)
    (hQ : ∀ i : Fin u, TaggedScalarRefinement Q (j i) (fun a => vfAt (f a).val i))
    (c : Fin (p+(m+d)) → M) :
    (MixedScalarFamilies.family (allConstantAttachment Q j) c).Finite := by
  let R := allConstantCode Q j
  let E := allConstantAttachment Q j
  by_cases hne : (MixedScalarFamilies.family E c).Nonempty
  · obtain ⟨x₀,b₀,hctx₀,_⟩ := hne
    obtain ⟨a₀,ha₀⟩ := b₀.property
    let a₀A : A := ⟨a₀.val,allConstantDomain_subset Q j a₀.property⟩
    have hzero : ∀ i, Q.toFun a₀A (j i) = rv (0 : VF (M := M)) :=
      (mem_allConstantDomain Q j a₀A).mp a₀.property
    have hFin := all_constant_code_fibre_finite hκ hs G hsmall f hbij hf Q j hQ a₀A hzero
    apply (hFin.image (fun x : VF (M := M) => x.val)).subset
    rintro x ⟨b,hctx,hx⟩
    obtain ⟨a,ha⟩ := b.property
    let aA : A := ⟨a.val,allConstantDomain_subset Q j a.property⟩
    have hAtt : MixedScalarFamilies.context (R.attachment a) = MixedScalarFamilies.context (R.attachment a₀) :=
      (congrArg MixedScalarFamilies.context ha).trans
        (hctx.trans (hctx₀.symm.trans (congrArg MixedScalarFamilies.context ha₀).symm))
    obtain ⟨hc,hcode⟩ := (RVAttachment.context_eq_iff R a a₀).mp hAtt
    refine ⟨vfAt a.val 0,⟨aA,hc,hcode,rfl⟩,?_⟩
    exact (congrArg (fun q : Point (M := M) (p+1) (m+d) => (vfAt q 0).val) ha).trans hx
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty


/-- The finite-fibre assertion is discharged internally before the separating
RV code is constructed on the actual attached all-constant locus. -/
theorem all_constant_attachment_rv_code {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (f : Map A B) (hbij : Function.Bijective f)
    (hf : GammaGraphDefinable G (pointMapGraph f)) (Q : GammaRVMap G (carrier A) d)
    (j : Fin u → Fin d)
    (hQ : ∀ i : Fin u, TaggedScalarRefinement Q (j i) (fun a => vfAt (f a).val i)) :
    ∃ e : ℕ, ∃ P : GammaRVMap G (allConstantAttachment Q j) e,
      ∀ a b : allConstantAttachment Q j,
        MixedScalarFamilies.context a.val = MixedScalarFamilies.context b.val →
          P.toFun a = P.toFun b → a = b :=
  finite_mixed_family_rv_code hκ hs h00 G hsmall _ (allConstantAttachment_definable Q j)
    (allConstantAttachment_family_finite hκ hs G hsmall f hbij hf Q j hQ)

end IntegrationInACVF.Section5
