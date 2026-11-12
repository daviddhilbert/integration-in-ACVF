import IntegrationSection6.MixedRVBlockEquivalences
import Section5.GammaLift
import Section5.GammaLiftRelation

/-! Extend a full Gamma isomorphism by unchanged auxiliary RV labels.
This is an actual mixed-point bijection with its complete Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m k l a : ℕ}
variable {A : Set (Point (M := M) n m)} {D : Set (Point (M := M) k l)}

def mixedRVExtensionEquiv (e : A ≃ D) (a : ℕ) : mixedRVExtension A a ≃ mixedRVExtension D a :=
  (mixedRVBlockEquiv A a).trans ((Equiv.prodCongr e (Equiv.refl _)).trans (mixedRVBlockEquiv D a).symm)

theorem mixedRVExtensionEquiv_base (e : A ≃ D) (a : ℕ) (p : mixedRVExtension A a) :
    mixedRVBase (mixedRVExtensionEquiv e a p).val = (e ⟨mixedRVBase p.val,p.property⟩).val := by
  let x := e ⟨mixedRVBase p.val,p.property⟩
  change (x.val.1,Fin.append x.val.2 (mixedRVTail p.val) ∘ Fin.castAdd a) = x.val
  exact Prod.ext rfl (funext (fun j => Fin.append_left _ _ j))

theorem mixedRVExtensionEquiv_tail (e : A ≃ D) (a : ℕ) (p : mixedRVExtension A a) :
    mixedRVTail (mixedRVExtensionEquiv e a p).val = mixedRVTail p.val :=
  funext (fun j => Fin.append_right _ _ j)

def gammaIsoAppendRV (e : GammaIso B A D) (a : ℕ) : GammaIso B (mixedRVExtension A a) (mixedRVExtension D a) := by
  let E := mixedRVExtensionEquiv e.equiv a
  let L := gammaLogicInput B
  let ps := mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.castAdd a : Fin m → Fin (m+a)) B.real
  let qs := mixedCoordinatePointMap (id : Fin k → Fin k) (Fin.castAdd a : Fin l → Fin (l+a)) B.real
  have hh := e.graph.preimage_maps ps qs
  let pt := mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (Fin.natAdd m : Fin a → Fin (m+a)) B.real
  let qt := mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin k) (Fin.natAdd l : Fin a → Fin (l+a)) B.real
  have ht := (L.real_map_graph (Map.id (PresentedSet.univ (pointSpace (M := M) 0 a) B.real))).preimage_maps pt qt
  have hTail : GammaGraphDefinable B (fun (p : Point (M := M) n (m+a)) (q : Point (M := M) k (l+a)) =>
      mixedRVTail p = mixedRVTail q) := by
    apply GammaGraphDefinable.congr ht
    intro p q
    constructor
    · rintro ⟨z,hz,hq⟩
      exact congrArg Prod.snd (hz.symm.trans hq)
    · intro he
      exact ⟨⟨(Fin.elim0,mixedRVTail p),Set.mem_univ _⟩,
        Prod.ext (Subsingleton.elim _ _) rfl,Prod.ext (Subsingleton.elim _ _) he⟩
  refine ⟨E,?_⟩
  apply GammaGraphDefinable.congr (hh.inter hTail)
  intro p q
  change ((∃ u : A, u.val = mixedRVBase p ∧ (e.equiv u).val = mixedRVBase q) ∧ mixedRVTail p = mixedRVTail q) ↔ _
  constructor
  · rintro ⟨⟨u,hu,hq⟩,ht⟩
    have hp : mixedRVBase p ∈ A := hu ▸ u.property
    let v : mixedRVExtension A a := ⟨p,hp⟩
    have he : (⟨mixedRVBase p,hp⟩ : A) = u := Subtype.ext hu.symm
    refine ⟨v,rfl,mixedPoint_eq_of_base_tail ?_ ?_⟩
    · exact (mixedRVExtensionEquiv_base e.equiv a v).trans
        ((congrArg (fun u => (e.equiv u).val) he).trans hq)
    · exact (mixedRVExtensionEquiv_tail e.equiv a v).trans ht
  · rintro ⟨v,hv,hq⟩
    refine ⟨⟨⟨mixedRVBase v.val,v.property⟩,congrArg mixedRVBase hv,?_⟩,?_⟩
    · exact (mixedRVExtensionEquiv_base e.equiv a v).symm.trans (congrArg mixedRVBase hq)
    · exact (congrArg mixedRVTail hv).symm.trans
        ((mixedRVExtensionEquiv_tail e.equiv a v).symm.trans (congrArg mixedRVTail hq))

end IntegrationInACVF.Section6
