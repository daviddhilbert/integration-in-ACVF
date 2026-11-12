import IntegrationSection6.MixedVFParameterTotals
import IntegrationSection6.GammaFibreBijectionCompactness

/-! Pointwise Gamma isomorphisms of mixed fibres uniformize to an actual
Gamma isomorphism of their total spaces over a definable VF base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n m a b : ℕ}

def GammaSortedIso.congr {r s : ℕ} {sr : Fin r → SortTag} {ss : Fin s → SortTag}
    {D D' : Set (Fin r → M)} {E E' : Set (Fin s → M)} (e : GammaSortedIso B sr ss D E)
    (hD : D = D') (hE : E = E') : GammaSortedIso B sr ss D' E' := by
  cases hD
  cases hE
  exact e

theorem gamma_mixed_fibre_compactness_restricted {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (U : Set (Point (M := M) (p+n) a)) (V : Set (Point (M := M) (p+m) b))
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V)
    (hrow : ∀ x : A, Nonempty (GammaIso ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩
      (vfParameterFibre U x.val.1) (vfParameterFibre V x.val.1))) :
    Nonempty (GammaIso B {q | (q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A ∧ q ∈ U}
      {q | (q.1 ∘ Fin.castAdd m,Fin.elim0) ∈ A ∧ q ∈ V}) := by
  have hD := gamma_mixedVFParameterDomain U hU
  have hE := gamma_mixedVFParameterDomain V hV
  obtain ⟨e⟩ := gamma_fibre_bijection_compactness hκ hs hr hg
    (gamma_raw_vf_parameter_base hA) hD hE (by
      rintro z ⟨x,hx,rfl⟩
      obtain ⟨f⟩ := hrow ⟨x,hx⟩
      exact ⟨(IntegrationInACVF.Section6.GammaIso.toSortedIso f).congr (mixedVFParameterDomain_row U x.1).symm
        (mixedVFParameterDomain_row V x.1).symm⟩)
  let f := e.toPointIso (finCongr (Nat.add_assoc p n a)) (finCongr (Nat.add_assoc p m b))
    mixedVFParameterSort_cast mixedVFParameterSort_cast
    (fun z hz => hD.proper z hz.2) (fun z hz => hE.proper z hz.2)
  exact ⟨f.congr (mixedVFParameterTotal_points A U) (mixedVFParameterTotal_points A V)⟩

theorem gamma_mixed_fibre_compactness {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (U : Set (Point (M := M) (p+n) a)) (V : Set (Point (M := M) (p+m) b))
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V)
    (hUA : ∀ q ∈ U, (q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A)
    (hVA : ∀ q ∈ V, (q.1 ∘ Fin.castAdd m,Fin.elim0) ∈ A)
    (hrow : ∀ x : A, Nonempty (GammaIso ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩
      (vfParameterFibre U x.val.1) (vfParameterFibre V x.val.1))) : Nonempty (GammaIso B U V) := by
  obtain ⟨e⟩ := gamma_mixed_fibre_compactness_restricted hκ hs hr hg A hA U V hU hV hrow
  have heU : {q | (q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A ∧ q ∈ U} = U := by
    ext q
    exact ⟨And.right,fun h => ⟨hUA q h,h⟩⟩
  have heV : {q | (q.1 ∘ Fin.castAdd m,Fin.elim0) ∈ A ∧ q ∈ V} = V := by
    ext q
    exact ⟨And.right,fun h => ⟨hVA q h,h⟩⟩
  exact ⟨e.congr heU heV⟩

end IntegrationInACVF.Section6
