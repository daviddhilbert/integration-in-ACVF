import IntegrationSection6.MixedVFParameterDomains

/-! The sorted total-space construction is exactly the inherited mixed
space, restricted to the stated VF parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {p n a : ℕ}

theorem rawVFParameter_injective : Function.Injective (rawVFParameter (M := M) (p := p)) := by
  intro x y h
  apply Prod.ext
  · funext j
    exact Subtype.ext (congrFun h j)
  · exact Subsingleton.elim _ _

theorem rawVFParameter_mem_image (A : Set (Point (M := M) p 0)) (x : Point (M := M) p 0) :
    rawVFParameter x ∈ rawVFParameter '' A ↔ x ∈ A := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact rawVFParameter_injective he ▸ hy
  · exact fun hx => ⟨x,hx,rfl⟩

theorem mixedVFParameterDomain_cast (U : Set (Point (M := M) (p+n) a)) (q : Point (M := M) (p+n) a) :
    gammaPointCode q ∘ Fin.cast (Nat.add_assoc p n a).symm ∈ mixedVFParameterDomain U ↔ q ∈ U := by
  change (_ ∈ gammaPointCode '' U ∧ _ ∈ sortedUniverse _) ↔ _
  have hcast : (gammaPointCode q ∘ Fin.cast (Nat.add_assoc p n a).symm) ∘ Fin.cast (Nat.add_assoc p n a) =
      gammaPointCode q := by
    funext j
    simp only [Function.comp_apply,Fin.cast_cast,Fin.cast_eq_self]
  rw [hcast]
  constructor
  · rintro ⟨⟨r,hr,he⟩,_⟩
    exact gammaPointCode_injective he ▸ hr
  · intro hq
    refine ⟨⟨q,hq,rfl⟩,?_⟩
    intro j
    have hs := congrFun (mixedVFParameterSort_cast (p := p) (n := n) (a := a))
      (Fin.cast (Nat.add_assoc p n a).symm j)
    simp only [Function.comp_apply,Fin.cast_cast,Fin.cast_eq_self] at hs
    rw [hs]
    exact gammaPointCode_proper q _

theorem mixedVFParameterCode_prefix (q : Point (M := M) (p+n) a) :
    (gammaPointCode q ∘ Fin.cast (Nat.add_assoc p n a).symm) ∘ Fin.castAdd (n+a) =
      rawVFParameter (q.1 ∘ Fin.castAdd n,Fin.elim0) := by
  funext j
  have hi : Fin.cast (Nat.add_assoc p n a).symm (Fin.castAdd (n+a) j) =
      Fin.castAdd a (Fin.castAdd n j) := Fin.ext rfl
  change gammaPointCode q (Fin.cast (Nat.add_assoc p n a).symm (Fin.castAdd (n+a) j)) = _
  rw [hi]
  exact Fin.append_left _ _ _

theorem mixedVFParameterTotal_points (A : Set (Point (M := M) p 0))
    (U : Set (Point (M := M) (p+n) a)) :
    {q : Point (M := M) (p+n) a | gammaPointCode q ∘ (finCongr (Nat.add_assoc p n a)).symm ∈
      rawRowTotal (rawVFParameter '' A) (mixedVFParameterDomain U)} =
      {q | (q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A ∧ q ∈ U} := by
  ext q
  change ((gammaPointCode q ∘ Fin.cast (Nat.add_assoc p n a).symm) ∘ Fin.castAdd (n+a) ∈ rawVFParameter '' A ∧
    gammaPointCode q ∘ Fin.cast (Nat.add_assoc p n a).symm ∈ mixedVFParameterDomain U) ↔
      ((q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A ∧ q ∈ U)
  rw [mixedVFParameterCode_prefix,mixedVFParameterDomain_cast,rawVFParameter_mem_image]

end IntegrationInACVF.Section6
