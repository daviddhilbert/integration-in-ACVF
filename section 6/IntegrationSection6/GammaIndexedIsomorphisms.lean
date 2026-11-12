import IntegrationSection6.IndexedEquivalences
import IntegrationSection6.GammaFiniteGraphIsomorphisms

/-! Fibrewise charts with their full joint Gamma graph assemble to actual
isomorphisms in RV[k]. Weight balance is preserved by appending the same
base volume to the two fibre volumes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {b a c d n : ℕ}

def GammaFiniteGraphPresentation.domainEquiv {a n : ℕ}
    {D : Set (Fin a → RV (M := M))}
    {R : (Fin a → RV (M := M)) → (Fin n → RV (M := M)) → Prop}
    (P : GammaFiniteGraphPresentation B a n D R) : P.domain ≃ D where
  toFun u := ⟨u.val,(Set.ext_iff.mp P.domain_eq u.val).mp u.property⟩
  invFun u := ⟨u.val,(Set.ext_iff.mp P.domain_eq u.val).mpr u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rawWeight_rv_append (t : Fin d → RV (M := M)) (s : Fin n → RV (M := M)) :
    rawWeight (rvValues (Fin.append t s)) = rawWeight (rvValues t) + rawWeight (rvValues s) := by
  unfold rawWeight rvValues
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]

def gammaIndexedIso
    (T : Set (Fin b → RV (M := M)))
    (D : (Fin b → RV (M := M)) → Set (Fin a → RV (M := M)))
    (E : (Fin b → RV (M := M)) → Set (Fin c → RV (M := M)))
    (f : (Fin b → RV (M := M)) → (Fin d → RV (M := M)))
    (g : (Fin b → RV (M := M)) → (Fin a → RV (M := M)) → (Fin n → RV (M := M)))
    (h : (Fin b → RV (M := M)) → (Fin c → RV (M := M)) → (Fin n → RV (M := M)))
    (P : GammaFiniteGraphPresentation B (b+a) (d+n) (indexedDomain T D)
      (fun w z => w ∈ indexedDomain T D ∧ indexedVolume f g w = z))
    (Q : GammaFiniteGraphPresentation B (b+c) (d+n) (indexedDomain T E)
      (fun w z => w ∈ indexedDomain T E ∧ indexedVolume f h w = z))
    (e : ∀ t : T, D t.val ≃ E t.val)
    (hΓ : GammaGraphDefinable B (fun (p : Point (M := M) 0 (b+a)) (q : Point (M := M) 0 (b+c)) =>
      ∃ w : indexedDomain T D, w.val = p.2 ∧ (indexedEquiv T D E e w).val = q.2))
    (hw : ∀ t : T, ∀ u : D t.val,
      rawWeight (rvValues (g t.val u.val)) = rawWeight (rvValues (h t.val (e t u).val))) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  let e' := P.domainEquiv.trans ((indexedEquiv T D E e).trans Q.domainEquiv.symm)
  have hPvol (u : P.domain) : (P.volume u).val = indexedVolume f g u.val :=
    ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2.2.symm
  have hQvol (v : Q.domain) : (Q.volume v).val = indexedVolume f h v.val :=
    ((Q.graph_iff v.val (Q.volume v).val).mp ⟨v,rfl,rfl⟩).2.2.symm
  refine FiniteRV.gammaIsoOfFiniteEquiv P.toGamma Q.toGamma e' ?_ ?_
  · apply GammaGraphDefinable.congr hΓ
    intro p q
    constructor
    · rintro ⟨w,hp,hq⟩
      exact ⟨P.domainEquiv.symm w,hp,hq⟩
    · rintro ⟨u,hp,hq⟩
      exact ⟨P.domainEquiv u,hp,hq⟩
  · intro u
    change rawWeight (fun j => ((P.volume u).val j).val) =
      rawWeight (fun j => ((Q.volume (e' u)).val j).val)
    rw [hPvol,hQvol]
    change rawWeight (rvValues (indexedVolume f g u.val)) =
      rawWeight (rvValues (indexedVolume f h (e' u).val))
    simp only [indexedVolume,rawWeight_rv_append]
    have hl : indexedLeft (e' u).val = indexedLeft u.val :=
      indexedEquiv_left T D E e (P.domainEquiv u)
    have hr : indexedRight (e' u).val =
        (e ⟨indexedLeft u.val,(P.domainEquiv u).property.1⟩
          ⟨indexedRight u.val,(P.domainEquiv u).property.2⟩).val :=
      indexedEquiv_right T D E e (P.domainEquiv u)
    rw [hl,hr]
    exact congrArg (fun v => rawWeight (rvValues (f (indexedLeft u.val))) + v)
      (hw ⟨indexedLeft u.val,(P.domainEquiv u).property.1⟩
        ⟨indexedRight u.val,(P.domainEquiv u).property.2⟩)

end IntegrationInACVF.Section6
