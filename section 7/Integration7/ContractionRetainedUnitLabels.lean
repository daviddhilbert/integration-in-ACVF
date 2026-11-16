module

public import Integration7.PreparedIndexedRetainedLabels
public import Integration7.ContractionRetainedDensityLabels

@[expose] public section

/-! A literal retained unit label remains the literal unit after a
specified contraction or an indexed prepared-family construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a k : ℕ}

theorem normalized_contraction_retained_label_unit
    {n : ℕ} {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (δ : Fin a)
    (hδ : ∀ q : A, (q.val.2 δ).val = iRVOne) :
    ∀ u : rvObjectDomain T.normalizedObject,
      (u.val (FiniteRV.contractionOldLabelIndex T δ)).val = iRVOne := by
  intro u
  obtain ⟨q,rfl⟩ := standard_normalized_contraction_map_surjective T u
  rw [FiniteRV.contraction_oldLabels]
  exact hδ q

theorem prepared_indexed_retained_label_unit
    (A : DefSet (M := M) S p 0) (Z : DefSet (M := M) S p l) (K : SpecialBijection A Z)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv))
    (hRows : ∀ q : Z, GammaSchemaRowAgreement F (rawVFParameter (K.inverseMap q).val) G (rawPreparedKey q.val))
    (BP : PreparedIndexPresentation B Z) (J : G.IndexedPresentation BP)
    (U : DefSet (M := M) S p a) (hSource : carrier U = vfSchemaSource (carrier A) F)
    (δ : Fin a) (hδ : ∀ u : U, (u.val.2 δ).val = iRVOne) :
    ∀ u : J.domain, (u.val (Fin.natAdd (p+l) δ)).val = iRVOne := by
  intro u
  obtain ⟨q,hq⟩ := (J.domain_eq.le u.property).1
  have hr := (J.domain_eq.le u.property).2
  have hParam := congrArg (fun r : Fin (p+l) → RV (M := M) => fun j => (r j).val) hq.symm
  have hrF : indexedRight u.val ∈ F.rowDomain (rawVFParameter (K.inverseMap q).val) := by
    rw [(hRows q).domains]
    exact (congrArg (fun t : Fin (p+l) → M => indexedRight u.val ∈ G.rowDomain t) hParam).mp hr
  let x := K.inverseMap q
  have hx : (x.val.1,Fin.elim0) ∈ carrier A := by
    have he : (x.val.1,Fin.elim0) = x.val := Prod.ext rfl (Subsingleton.elim _ _)
    exact he.symm ▸ x.property
  have hp : (x.val.1,indexedRight u.val) ∈ carrier U := by
    rw [hSource]
    exact ⟨hx,hrF⟩
  exact hδ ⟨(x.val.1,indexedRight u.val),hp⟩


end IntegrationInACVF.Section7
