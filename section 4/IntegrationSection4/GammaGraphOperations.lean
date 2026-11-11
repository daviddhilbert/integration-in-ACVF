import IntegrationSection4.GammaTupleGraphs

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaGraphOperations

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem inter (G : GammaParameters.Base (M := M)) {n m u w : ℕ}
    {r t : Point (M := M) n m → Point (M := M) u w → Prop}
    (hr : GammaGraphDefinable G r) (ht : GammaGraphDefinable G t) :
    GammaGraphDefinable G (fun p q => r p q ∧ t p q) := by
  have h := GammaTupleGraphs.relation_of_full G _ (FullBaseAtomicity.OverBase.inter
    (GammaTupleGraphs.rawGraph_definable G r hr) (GammaTupleGraphs.rawGraph_definable G t ht))
  apply GammaGraphDefinable.congr h
  intro p q
  exact and_congr (GammaTupleGraphs.rawGraph_iff r p q) (GammaTupleGraphs.rawGraph_iff t p q)

theorem reindex_rv_output (G : GammaParameters.Base (M := M)) {n m d e : ℕ}
    {r : Point (M := M) n m → Point (M := M) 0 d → Prop}
    (hr : GammaGraphDefinable G r) (ρ : Fin d → Fin e) :
    GammaGraphDefinable G (fun (p : Point (M := M) n m) (q : Point (M := M) 0 e) =>
      r p (Fin.elim0,q.2 ∘ ρ)) := by
  let σ : Fin ((n+m)+(0+d)) → Fin ((n+m)+(0+e)) :=
    Fin.addCases (fun i => Fin.castAdd (0+e) i)
      (Fin.addCases (fun i : Fin 0 => i.elim0) (fun i => Fin.natAdd (n+m) (Fin.natAdd 0 (ρ i))))
  have h := GammaTupleGraphs.relation_of_full G _ (FullBaseAtomicity.OverBase.preimage_comp
    (GammaTupleGraphs.rawGraph_definable G r hr) σ)
  apply GammaGraphDefinable.congr h
  intro p q
  change (Fin.append (gammaPointCode p) (gammaPointCode q) ∘ σ ∈ GammaTupleGraphs.rawGraph r) ↔ _
  have he : Fin.append (gammaPointCode p) (gammaPointCode q) ∘ σ =
      Fin.append (gammaPointCode p) (gammaPointCode (Fin.elim0,q.2 ∘ ρ)) := by
    funext i
    cases i using Fin.addCases with
    | left i => simp only [Function.comp_apply,σ,Fin.addCases_left,Fin.append_left]
    | right i =>
      cases i using Fin.addCases with
      | left i => exact i.elim0
      | right i => simp only [Function.comp_apply,σ,Fin.addCases_right,Fin.append_right,gammaPointCode,Fin.append_right]
  rw [he]
  exact GammaTupleGraphs.rawGraph_iff r _ _

end IntegrationInACVF.Section4.GammaGraphOperations
