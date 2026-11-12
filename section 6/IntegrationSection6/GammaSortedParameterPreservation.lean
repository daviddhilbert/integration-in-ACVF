import IntegrationSection6.GammaFibreBijectionCompactness
import IntegrationSection6.GammaSortedPointIsomorphisms
import IntegrationSection6.GammaCoordinateValues

/-! The compactness construction is a bijection over its parameter base,
and the explicit point-coordinate conversion preserves that information. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
variable {sp : Fin p → SortTag} {sx : Fin a → SortTag} {sy : Fin b → SortTag}
variable {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)} {A : Set (Fin p → M)}

theorem gammaSortedTotalEquiv_prefix (C : GammaSortedBijectionChart B sp sx sy)
    (hE : DefinableOverBase B (Fin.append sp sy) E) (hC : ∀ z ∈ A, C.valid D E z)
    (u : rawRowTotal A D) :
    (gammaSortedTotalEquiv C hE hC u).val ∘ Fin.castAdd b = u.val ∘ Fin.castAdd a := by
  change (Fin.append (u.val ∘ Fin.castAdd a) _ ∘ Fin.castAdd b) = _
  exact funext (fun j => Fin.append_left _ _ j)

theorem gamma_fibre_bijection_compactness_preserving {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hA : DefinableOverBase B sp A)
    (hD : DefinableOverBase B (Fin.append sp sx) D) (hE : DefinableOverBase B (Fin.append sp sy) E)
    (hrow : ∀ z ∈ A, Nonempty (GammaSortedIso ⟨B.real ∪ Set.range z,B.gamma⟩ sx sy
      {x : Fin a → M | Fin.append z x ∈ D} {y : Fin b → M | Fin.append z y ∈ E})) :
    ∃ e : GammaSortedIso B (Fin.append sp sx) (Fin.append sp sy) (rawRowTotal A D) (rawRowTotal A E),
      ∀ u, (e.equiv u).val ∘ Fin.castAdd b = u.val ∘ Fin.castAdd a := by
  obtain ⟨C,hC⟩ := gamma_uniform_bijection_chart hκ hs hr hg A hA hD hE (by
    intro z hz
    obtain ⟨e⟩ := hrow z hz
    exact gamma_promote_row_bijection z (hA.proper z hz) e.equiv
      {w | ∃ u, Fin.append u.val (e.equiv u).val = w} e.graph e.graph_iff)
  exact ⟨gammaSortedTotalIso C hA hE hC,gammaSortedTotalEquiv_prefix C hE hC⟩

theorem gammaSortedIso_toPointIso_code {a b n m u v : ℕ}
    {sa : Fin a → SortTag} {sb : Fin b → SortTag} {D : Set (Fin a → M)} {E : Set (Fin b → M)}
    (e : GammaSortedIso B sa sb D E) (ρ : Fin (n+m) ≃ Fin a) (τ : Fin (u+v) ≃ Fin b)
    (hρ : sa ∘ ρ = gammaPointSort n m) (hτ : sb ∘ τ = gammaPointSort u v)
    (hD : ∀ z ∈ D, ∀ i, sortEval (sa i) (z i)) (hE : ∀ z ∈ E, ∀ i, sortEval (sb i) (z i))
    (x : {p : Point (M := M) n m | gammaPointCode p ∘ ρ.symm ∈ D}) :
    gammaPointCode ((e.toPointIso ρ τ hρ hτ hD hE).equiv x).val =
      (e.equiv ⟨gammaPointCode x.val ∘ ρ.symm,x.property⟩).val ∘ τ := by
  change gammaPointCode ((sortedPointDomainEquiv τ hτ hE).symm
    (e.equiv ((sortedPointDomainEquiv ρ hρ hD) x))).val = _
  exact sortedPointDomainEquiv_symm_code τ hτ hE _

theorem gammaIsoCongr_value {n a r b : ℕ} {A A' : Set (Point (M := M) n a)}
    {C C' : Set (Point (M := M) r b)} (e : GammaIso B A C) (hA : A = A') (hC : C = C') (x : A') :
    ((e.congr hA hC).equiv x).val = (e.equiv ((Equiv.subtypeEquivRight (fun p : Point (M := M) n a =>
      Iff.of_eq (congrArg (fun S : Set (Point (M := M) n a) => p ∈ S) hA))).symm x)).val := by
  cases hA
  cases hC
  rfl

end IntegrationInACVF.Section6
