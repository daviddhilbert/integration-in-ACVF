import IntegrationSection6.GammaSortedParameterPreservation
import IntegrationSection6.MixedVFFibreCompactness
import IntegrationSection6.VFParameterFibreIsomorphisms

/-! Fibrewise compactness can preserve all VF parameters, as required
for changing representatives before a projection pushforward. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n m a b : ℕ}

theorem vfParametersPreserved_congr {U U' : Set (Point (M := M) (p+n) a)}
    {V V' : Set (Point (M := M) (p+m) b)} (e : GammaIso B U V) (hp : VFParametersPreserved e)
    (hU : U = U') (hV : V = V') : VFParametersPreserved (e.congr hU hV) := by
  intro u j
  rw [gammaIsoCongr_value]
  exact hp _ j

theorem gamma_mixed_fibre_uniformity_restricted {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (U : Set (Point (M := M) (p+n) a)) (V : Set (Point (M := M) (p+m) b))
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V)
    (hrow : ∀ x : A, Nonempty (GammaIso ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩
      (vfParameterFibre U x.val.1) (vfParameterFibre V x.val.1))) :
    ∃ e : GammaIso B {q | (q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A ∧ q ∈ U}
      {q | (q.1 ∘ Fin.castAdd m,Fin.elim0) ∈ A ∧ q ∈ V}, VFParametersPreserved e := by
  have hD := gamma_mixedVFParameterDomain (p := p) (n := n) U hU
  have hE := gamma_mixedVFParameterDomain (p := p) (n := m) V hV
  obtain ⟨e,he⟩ := gamma_fibre_bijection_compactness_preserving hκ hs hr hg
    (gamma_raw_vf_parameter_base hA) hD hE (by
      rintro z ⟨x,hx,rfl⟩
      obtain ⟨f⟩ := hrow ⟨x,hx⟩
      exact ⟨(IntegrationInACVF.Section6.GammaIso.toSortedIso f).congr
        (mixedVFParameterDomain_row U x.1).symm (mixedVFParameterDomain_row V x.1).symm⟩)
  let ρ := finCongr (Nat.add_assoc p n a)
  let τ := finCongr (Nat.add_assoc p m b)
  let f := e.toPointIso ρ τ mixedVFParameterSort_cast mixedVFParameterSort_cast
    (fun z hz => hD.proper z hz.2) (fun z hz => hE.proper z hz.2)
  have hf : VFParametersPreserved f := by
    intro u j
    let ru := (⟨gammaPointCode u.val ∘ ρ.symm,u.property⟩ : rawRowTotal (rawVFParameter '' A) (mixedVFParameterDomain U))
    have hc := gammaSortedIso_toPointIso_code e ρ τ mixedVFParameterSort_cast mixedVFParameterSort_cast
      (fun z hz => hD.proper z hz.2) (fun z hz => hE.proper z hz.2) u
    have ht : gammaPointCode (f.equiv u).val ∘ τ.symm = (e.equiv ru).val := by
      rw [hc]
      funext i
      simp only [Function.comp_apply,Equiv.apply_symm_apply]
      rfl
    have hpref : rawVFParameter ((f.equiv u).val.1 ∘ Fin.castAdd m,Fin.elim0) =
        rawVFParameter (u.val.1 ∘ Fin.castAdd n,Fin.elim0) := by
      rw [← mixedVFParameterCode_prefix (f.equiv u).val,← mixedVFParameterCode_prefix u.val]
      change (gammaPointCode (f.equiv u).val ∘ τ.symm) ∘ Fin.castAdd (m+b) =
        (gammaPointCode u.val ∘ ρ.symm) ∘ Fin.castAdd (n+a)
      rw [ht]
      exact he ru
    exact Subtype.ext (congrFun hpref j)
  exact ⟨f.congr (mixedVFParameterTotal_points A U) (mixedVFParameterTotal_points A V),
    vfParametersPreserved_congr f hf _ _⟩

theorem gamma_mixed_fibre_uniformity {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (U : Set (Point (M := M) (p+n) a)) (V : Set (Point (M := M) (p+m) b))
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V)
    (hUA : ∀ q ∈ U, (q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A)
    (hVA : ∀ q ∈ V, (q.1 ∘ Fin.castAdd m,Fin.elim0) ∈ A)
    (hrow : ∀ x : A, Nonempty (GammaIso ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩
      (vfParameterFibre U x.val.1) (vfParameterFibre V x.val.1))) :
    ∃ e : GammaIso B U V, VFParametersPreserved e := by
  obtain ⟨e,he⟩ := gamma_mixed_fibre_uniformity_restricted hκ hs hr hg A hA U V hU hV hrow
  have heU : {q | (q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A ∧ q ∈ U} = U := by
    ext q
    exact ⟨And.right,fun h => ⟨hUA q h,h⟩⟩
  have heV : {q | (q.1 ∘ Fin.castAdd m,Fin.elim0) ∈ A ∧ q ∈ V} = V := by
    ext q
    exact ⟨And.right,fun h => ⟨hVA q h,h⟩⟩
  exact ⟨e.congr heU heV,vfParametersPreserved_congr e he heU heV⟩

end IntegrationInACVF.Section6
