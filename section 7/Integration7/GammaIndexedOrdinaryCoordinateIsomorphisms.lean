module

public import Integration7.GammaIndexedOrdinaryRowBijections
public import IntegrationSection6.GammaIndexedIsomorphisms
public import IntegrationSection6.GammaSchemaIndexedPresentations

@[expose] public section

/-! The actual indexed ordinary-row bijection preserves the whole base
volume tuple. Empty fibre volume contributes no coordinates or weight. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d : ℕ}

def pureRVLabelPointEquiv (D : Set (Fin a → RV (M := M))) :
    D ≃ {q : Point (M := M) 0 a | q.2 ∈ D} where
  toFun u := ⟨(Fin.elim0,u.val),u.property⟩
  invFun q := ⟨q.val.2,q.property⟩
  left_inv _ := rfl
  right_inv q := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)

variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable (BP : GammaFiniteGraphPresentation B p d T R)
variable (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
variable (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
variable (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
variable (e : GammaIso B
  {q : Point (M := M) 0 (p+a) | q.2 ∈ indexedDomain T (fun t => F.rowDomain (rvValues t))}
  {q : Point (M := M) 0 (p+b) | q.2 ∈ indexedDomain T (fun t => G.rowDomain (rvValues t))})

def indexedOrdinaryLabelEquiv : P.domain ≃ Q.domain :=
  P.domainEquiv.trans ((pureRVLabelPointEquiv _).trans
    (e.equiv.trans ((pureRVLabelPointEquiv _).symm.trans Q.domainEquiv.symm)))

theorem indexed_ordinary_label_equiv_prefix
    (hPrefix : ∀ q, (e.equiv q).val.2 ∘ Fin.castAdd b = q.val.2 ∘ Fin.castAdd a)
    (u : P.domain) :
    indexedLeft (indexedOrdinaryLabelEquiv BP F G P Q e u).val = indexedLeft u.val :=
  hPrefix ((pureRVLabelPointEquiv _) (P.domainEquiv u))

theorem indexed_ordinary_label_equiv_graph :
    GammaGraphDefinable B (fun (x : Point (M := M) 0 (p+a)) (y : Point (M := M) 0 (p+b)) =>
      ∃ u : P.domain, u.val = x.2 ∧ (indexedOrdinaryLabelEquiv BP F G P Q e u).val = y.2) := by
  apply GammaGraphDefinable.congr e.graph
  intro x y
  constructor
  · rintro ⟨u,hu,hv⟩
    let x := P.domainEquiv.symm ⟨u.val.2,u.property⟩
    have hx : (pureRVLabelPointEquiv _) (P.domainEquiv x) = u := by
      change (pureRVLabelPointEquiv _) (P.domainEquiv (P.domainEquiv.symm _)) = u
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
    refine ⟨x,congrArg (fun z : Point (M := M) 0 (p+a) => z.2) hu,?_⟩
    change (e.equiv ((pureRVLabelPointEquiv _) (P.domainEquiv x))).val.2 = y.2
    exact (congrArg (fun z => (e.equiv z).val.2) hx).trans
      (congrArg (fun z : Point (M := M) 0 (p+b) => z.2) hv)
  · rintro ⟨u,hu,hv⟩
    exact ⟨(pureRVLabelPointEquiv _) (P.domainEquiv u),
      Prod.ext (Subsingleton.elim _ _) hu,Prod.ext (Subsingleton.elim _ _) hv⟩

theorem indexed_ordinary_label_equiv_volume
    (hPrefix : ∀ q, (e.equiv q).val.2 ∘ Fin.castAdd b = q.val.2 ∘ Fin.castAdd a)
    (u : P.domain) :
    (Q.volume (indexedOrdinaryLabelEquiv BP F G P Q e u)).val = (P.volume u).val := by
  let v := indexedOrdinaryLabelEquiv BP F G P Q e u
  have hPV : (P.volume u).val = indexedVolume BP.totalVolume (fun t => F.rowValue (rvValues t)) u.val :=
    ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2.2.symm
  have hQV : (Q.volume v).val = indexedVolume BP.totalVolume (fun t => G.rowValue (rvValues t)) v.val :=
    ((Q.graph_iff v.val (Q.volume v).val).mp ⟨v,rfl,rfl⟩).2.2.symm
  have hLeft := indexed_ordinary_label_equiv_prefix BP F G P Q e hPrefix u
  rw [hPV,hQV]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => Fin.elim0 j) i
  simp only [indexedVolume,Fin.append_left]
  rw [hLeft]

end IntegrationInACVF.Section7
