import IntegrationSection6.GammaSortedTotalBijections

/-! Pointwise definable bijections over the actual parameter-extended bases
uniformize to an original-base definable bijection of total spaces. Only
original real/Gamma names are bounded; the parameter set may be infinite. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
variable {sp : Fin p → SortTag} {sx : Fin a → SortTag} {sy : Fin b → SortTag}
variable {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)} {A : Set (Fin p → M)}

theorem GammaSortedIso.graph_iff {C : Base (M := M)} {D : Set (Fin a → M)} {E : Set (Fin b → M)}
    (e : GammaSortedIso C sx sy D E) (x : Fin a → M) (y : Fin b → M) :
    (∃ u : D, Fin.append u.val (e.equiv u).val = Fin.append x y) ↔
      ∃ u : D, u.val = x ∧ (e.equiv u).val = y := by
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨u,funext (fun j => by simpa only [Fin.append_left] using congrFun hu (Fin.castAdd b j)),
      funext (fun j => by simpa only [Fin.append_right] using congrFun hu (Fin.natAdd a j))⟩
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨u,rfl⟩

theorem gamma_fibre_bijection_compactness {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (hA : DefinableOverBase B sp A)
    (hD : DefinableOverBase B (Fin.append sp sx) D) (hE : DefinableOverBase B (Fin.append sp sy) E)
    (hrow : ∀ z ∈ A, Nonempty (GammaSortedIso ⟨B.real ∪ Set.range z,B.gamma⟩ sx sy
      {x : Fin a → M | Fin.append z x ∈ D} {y : Fin b → M | Fin.append z y ∈ E})) :
    Nonempty (GammaSortedIso B (Fin.append sp sx) (Fin.append sp sy) (rawRowTotal A D) (rawRowTotal A E)) := by
  obtain ⟨C,hC⟩ := gamma_uniform_bijection_chart hκ hs hreal hgamma A hA hD hE (by
    intro z hz
    obtain ⟨e⟩ := hrow z hz
    exact gamma_promote_row_bijection z (hA.proper z hz) e.equiv
      {w | ∃ u, Fin.append u.val (e.equiv u).val = w} e.graph (e.graph_iff))
  exact ⟨gammaSortedTotalIso C hA hE hC⟩

end IntegrationInACVF.Section6
