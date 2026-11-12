import IntegrationSection6.FiniteGammaObjects
import IntegrationSection5.RVContractionGamma

/-! Mutually contractible VF-preserving actual bijections induce
volume-preserving isomorphisms of finite RV-pullback objects in any arity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b : ℕ}

def gammaVFContractiblePullbackIso (hBS : B.real ⊆ S)
    {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U)))
    (hVF : Map.FiniteFibres (rvObjectVolume (pullbackObject V)))
    (f : Map U V) (hf : Function.Bijective f) (hc : Contractible f)
    (hback : Contractible (Map.inverse f hf)) (hF : GammaGraphDefinable B (pointMapGraph f))
    (hPres : ∀ u : U, (f u).val.1 = u.val.1) :
    GammaRVIso (gammaPullbackAt hBS U hU hUF).toGamma.toGammaRVObject
      (gammaPullbackAt hBS V hV hVF).toGamma.toGammaRVObject := by
  let P := gammaPullbackAt hBS U hU hUF
  let Q := gammaPullbackAt hBS V hV hVF
  apply gammaIsoOfFiniteEquiv P.toGamma Q.toGamma
    (Equiv.ofBijective (rvContractionMap f hc) (rvContractionMap_bijective f hf hc hback))
    (gamma_rvContractionMap_graph f hc hF)
  intro u
  obtain ⟨a,rfl⟩ := rawKeyImage_surjective U u
  change rawWeight (fun j => ((rvObjectVolume (pullbackObject U) (Map.toImage (rawKeyMap U) a)).val j).val) =
    rawWeight (fun j => ((rvObjectVolume (pullbackObject V) (rvContractionMap f hc (Map.toImage (rawKeyMap U) a))).val j).val)
  rw [pullbackObject_value_key,rvContractionMap_volume_spec]
  exact congrArg (fun z : Fin n → VF (M := M) => rawWeight (fun j => (@rv M sM hM (z j)).val)) (hPres a).symm

end IntegrationInACVF.Section6.FiniteRV
