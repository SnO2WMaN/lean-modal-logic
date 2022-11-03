import tactic data.set
import prop.language prop.semantics prop.syntax
 
namespace prop

lemma axiomL_tautology (v φ) : φ ∈ AxiomL → (v ⊨ φ) := 
begin
  intro h,
  cases h,
  case P1: {
    sorry
  },
  case P2: {
    sorry
  },
  case P3: {
    sorry
  },
end

theorem soundness (v φ) : ⊢ₗ φ → v ⊨ φ :=
begin
  intro he,
  induction he,
  
  case in_axioms : _ _ hA {
    exact @axiomL_tautology v _ hA,
  },

  case in_context :{
    sorry,
  },

  case mp :{
    sorry,
  },
end

end prop