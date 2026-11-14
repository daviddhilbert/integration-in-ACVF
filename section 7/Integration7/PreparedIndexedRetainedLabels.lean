import Integration7.GammaSliceLiftChartValues
import IntegrationSection6.GammaSchemaRowAgreement

/-! Every prepared indexed label comes from an actual original family
row. A nonzero original density label therefore stays nonzero before
and after the selected/VF volume blocks are swapped. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a k : ℕ}

theorem prepared_indexed_retained_label_nonzero
    (A : DefSet (M := M) S p 0) (Z : DefSet (M := M) S p l) (K : SpecialBijection A Z)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv))
    (hRows : ∀ q : Z, GammaSchemaRowAgreement F (rawVFParameter (K.inverseMap q).val) G (rawPreparedKey q.val))
    (BP : PreparedIndexPresentation B Z) (J : G.IndexedPresentation BP)
    (U : DefSet (M := M) S p a) (hSource : carrier U = vfSchemaSource (carrier A) F)
    (δ : Fin a) (hδ : ∀ u : U, (u.val.2 δ).val ≠ iRVZero) :
    ∀ u : J.domain, (u.val (Fin.natAdd (p+l) δ)).val ≠ iRVZero := by
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
