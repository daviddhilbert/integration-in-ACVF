import IntegrationSection3ACVF.CofiniteRVRows
import IntegrationSection3ACVF.FullRVClassRestriction
import IntegrationSection3ACVF.RVInverse
import IntegrationSection3.CofiniteClassMatching

/-! A definable bijection between unions of entire actual nonzero RV
value fibres induces a bijection of their Gamma indices. Dominant matches
are constructed in both directions; the inverse proves surjectivity. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVValueMatching

open FullRVValueFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def classes (I : Set (Values.Gamma (M := M))) (γ : I) : Set M := fibre γ.val

theorem class_subset (I : Set (Values.Gamma (M := M))) (γ : I) : classes I γ ⊆ Values.gammaPullback I := by
  intro x hx
  have hx0 := subset_nonzero γ.val hx
  have hEq := (mem_fibre_code γ.val x hx0).mp hx
  rw [GammaSyntax.mem_gammaPullback_iff]
  exact ⟨hx0,hEq.symm ▸ γ.property⟩

theorem matching_rows {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (I J : Set (Values.Gamma (M := M))) (g : M → M)
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g))
    (hbij : Set.BijOn g (Values.gammaPullback I) (Values.gammaPullback J)) :
    ∀ γ : I, ∃ η : J, CofiniteClassMatching.Matches (classes I) (classes J) g γ η := by
  intro γ
  let C := B.adjoin (Sum.inr γ.val)
  have hGγ : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (fibre γ.val) g) :=
    FullRVClassRestriction.graph_definable B (Values.gammaPullback I) g hG γ.val (class_subset I γ)
  have hOut (x : M) (hx : x ∈ fibre γ.val) : NonzeroRV (g x) :=
    ((GammaSyntax.mem_gammaPullback_iff J (g x)).mp (hbij.1 (class_subset I γ hx))).1
  obtain ⟨η,hCo,_⟩ := CofiniteRVRows.exists_unique_dominant hκ hs h00 C hsmall g γ.val hGγ hOut
  have hTarget := CofiniteRVRows.cofinite_target h00 C g γ.val η hGγ hOut
    (hbij.2.1.mono (class_subset I γ)) hCo
  obtain ⟨x,hx,hBad⟩ := ((fibre_infinite h00 γ.val).sdiff hCo).nonempty
  have hxRow : x ∈ CofiniteRVRows.row g γ.val η := by
    by_contra hn
    exact hBad ⟨hx,hn⟩
  have hJ : η ∈ J := by
    have h := ((GammaSyntax.mem_gammaPullback_iff J (g x)).mp (hbij.1 (class_subset I γ hx))).2
    exact hxRow.2 ▸ h
  refine ⟨⟨η,hJ⟩,?_,hTarget⟩
  apply hCo.subset
  intro z hz
  refine ⟨hz.1,?_⟩
  intro hr
  exact hz.2 ((mem_fibre_code η (g z) (hOut z hz.1)).mpr hr.2)

theorem exists_gamma_bijection {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (I J : Set (Values.Gamma (M := M))) (g : M → M)
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g))
    (hbij : Set.BijOn g (Values.gammaPullback I) (Values.gammaPullback J)) :
    ∃ e : I → J, Function.Bijective e ∧
      ∀ γ η, CofiniteClassMatching.Matches (classes I) (classes J) g γ η ↔ e γ = η := by
  let U := Values.gammaPullback I
  let V := Values.gammaPullback J
  let h := RVInverse.inverse U g
  have hImage : g '' U = V := hbij.image_eq
  have hH : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn V h) := by
    have hd := RVInverse.inverse_graph_definable B hbij.2.1 hG
    rwa [hImage] at hd
  have hLeft (x : M) (hx : x ∈ U) : h (g x) = x := RVInverse.inverse_on hbij.2.1 hx
  have hRight (y : M) (hy : y ∈ V) : g (h y) = y :=
    (RVInverse.inverse_right ((Set.ext_iff.mp hImage y).mpr hy)).2
  have hInv : Set.BijOn h V U := by
    refine ⟨?_,?_,?_⟩
    · intro y hy
      exact (RVInverse.inverse_right ((Set.ext_iff.mp hImage y).mpr hy)).1
    · have hi := RVInverse.inverse_injOn U g
      rwa [hImage] at hi
    · intro x hx
      exact ⟨g x,hbij.1 hx,hLeft x hx⟩
  have hRow := matching_rows hκ hs h00 B hsmall I J g hG hbij
  have hCol : ∀ η : J, ∃ γ : I, CofiniteClassMatching.Matches (classes I) (classes J) g γ η := by
    intro η
    obtain ⟨γ,hγ⟩ := matching_rows hκ hs h00 B hsmall J I h hH hInv η
    exact ⟨γ,CofiniteClassMatching.inverse_matches (classes I) (classes J) g h U V
      (class_subset I) (class_subset J) hLeft hRight hγ⟩
  exact CofiniteClassMatching.exists_bijection (classes I) (classes J) g U
    (class_subset I) hbij.2.1 (fun γ => fibre_infinite h00 γ.val) (fun η => fibre_infinite h00 η.val)
    (fun γ η hne => @fibres_disjoint M sM hM γ.val η.val (fun he => hne (Subtype.ext he)))
    (fun γ η hne => @fibres_disjoint M sM hM γ.val η.val (fun he => hne (Subtype.ext he))) hRow hCol

end IntegrationInACVF.Section3ACVF.RVValueMatching
