import IntegrationSection3ACVF.RVMatchUniformBound
import IntegrationSection3ACVF.RVMatchRowSemantics
import IntegrationSection3ACVF.FullBaseCounting

/-! The actual Gamma matching bijection has a full first-order graph over
the original interpreted base. Genuine uniform finite-side bounds turn
cofiniteness into finitely many distinct witnesses on every proper code pair. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.DefinableGammaMatching

open RVMatchCodeRelations FullRVValueFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def graph (I J : Set (Values.Gamma (M := M))) (e : I → J) (a : Fin 2 → Values.Gamma (M := M)) : Prop :=
  ∃ γ : I, ∃ η : J, γ.val = a 0 ∧ η.val = a 1 ∧ e γ = η

theorem hasMore_iff (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (I J : Set (Values.Gamma (M := M))) (g : M → M)
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g))
    (hbij : Set.BijOn g (Values.gammaPullback I) (Values.gammaPullback J))
    (e : I → J)
    (hMatch : ∀ γ η, CofiniteClassMatching.Matches (RVValueMatching.classes I) (RVValueMatching.classes J) g γ η ↔ e γ = η)
    (N : ℕ)
    (hBound : ∀ a : Fin 2 → M, GammaSyntax.Proper a →
      ((matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).Finite ∧
        (matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).ncard ≤ N) ∨
      ((sourceRow (Values.gammaPullback I) a \ matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).Finite ∧
        (sourceRow (Values.gammaPullback I) a \ matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).ncard ≤ N))
    (a : Fin 2 → M) (ha : GammaSyntax.Proper a) :
    a ∈ FullBaseCounting.hasMore (matchCodes (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g)) N ↔
      graph I J e (GammaSyntax.decode a) := by
  let H := ImaginaryBaseImages.graphOn (Values.gammaPullback I) g
  let R := matchRow H a
  have hCount : a ∈ FullBaseCounting.hasMore (matchCodes H) N ↔ ¬ (R.Finite ∧ R.ncard ≤ N) :=
    FullBaseCounting.hasMore_iff (matchCodes H) a N
  constructor
  · intro hMany
    have hNonempty : R.Nonempty := by
      obtain ⟨x,_,hRows⟩ := hMany
      exact ⟨x 0,hRows 0⟩
    obtain ⟨hI,hJ⟩ := RVMatchRowSemantics.nonempty_labels I J g hbij.1 a hNonempty
    have hCo : (sourceRow (Values.gammaPullback I) a \ R).Finite := by
      rcases hBound a ha with h | h
      · exact ((hCount.mp hMany) h).elim
      · exact h.1
    have hSource := sourceRow_eq I a ha hI
    have hCo' : (fibre (codeValue (a 0)) \ matchRow H a).Finite := by
      rwa [hSource] at hCo
    have hMatch' := (RVMatchRowSemantics.cofinite_matches_iff h00 B I J g hG hbij a ha hI hJ).mp hCo'
    exact ⟨⟨codeValue (a 0),hI⟩,⟨codeValue (a 1),hJ⟩,rfl,rfl,(hMatch _ _).mp hMatch'⟩
  · rintro ⟨γ,η,hγ,hη,he⟩
    change γ.val = codeValue (a 0) at hγ
    change η.val = codeValue (a 1) at hη
    have hI : codeValue (a 0) ∈ I := by rw [← hγ]; exact γ.property
    have hJ : codeValue (a 1) ∈ J := by rw [← hη]; exact η.property
    let γ' : I := ⟨codeValue (a 0),hI⟩
    let η' : J := ⟨codeValue (a 1),hJ⟩
    have hγ' : γ' = γ := Subtype.ext hγ.symm
    have hη' : η' = η := Subtype.ext hη.symm
    have hMatch' : CofiniteClassMatching.Matches (RVValueMatching.classes I) (RVValueMatching.classes J) g γ' η' := by
      rw [hγ',hη']
      exact (hMatch γ η).mpr he
    have hCo := (RVMatchRowSemantics.cofinite_matches_iff h00 B I J g hG hbij a ha hI hJ).mpr hMatch'
    have hRInf : R.Infinite := by
      apply ((fibre_infinite h00 (codeValue (a 0))).sdiff hCo).mono
      intro x hx
      by_contra hn
      exact hx.2 ⟨hx.1,hn⟩
    exact hCount.mpr (fun hFinite => hRInf hFinite.1)

theorem exists_definable_gamma_bijection {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (I J : Set (Values.Gamma (M := M))) (g : M → M)
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g))
    (hbij : Set.BijOn g (Values.gammaPullback I) (Values.gammaPullback J)) :
    ∃ e : I → J, Function.Bijective e ∧ FullGammaSyntax.Definable B (graph I J e) := by
  obtain ⟨e,hBijE,hMatch⟩ := RVValueMatching.exists_gamma_bijection hκ hs h00 B hsmall I J g hG hbij
  obtain ⟨N,hBound⟩ := RVMatchUniformBound.exists_bound hκ hs B hsmall I g hG
  have hR := matchCodes_definable B hG
  have hMany := FullBaseCounting.hasMore_definable B _ hR N
  have hProper := FullGammaSyntax.proper_definable (ι := Fin 2) B
  refine ⟨e,hBijE,?_⟩
  change FullBaseAtomicity.OverBase B {a : Fin 2 → M | GammaSyntax.Proper a ∧ graph I J e (GammaSyntax.decode a)}
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hProper hMany)
  intro a
  change (GammaSyntax.Proper a ∧ a ∈ FullBaseCounting.hasMore (matchCodes (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g)) N) ↔ _
  exact and_congr_right (fun ha => hasMore_iff h00 B I J g hG hbij e hMatch N hBound a ha)

end IntegrationInACVF.Section3ACVF.DefinableGammaMatching
