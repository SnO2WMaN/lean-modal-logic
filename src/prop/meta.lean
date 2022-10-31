import tactic data.set
import prop.language prop.semantics prop.syntax
 
namespace prop

lemma axiomL_tautology (φ) : φ ∈ AxiomL → (⊨ φ) := 
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

lemma sounds (φ) : ⊢ₗ φ → ⊨ φ :=
begin
  intro he,
  induction he,
  
  case in_axioms : _ _ hA {
    exact @axiomL_tautology _ hA,
  },

  case in_context :{
    sorry,
  },

  case mp :{
    sorry,
  },
end

lemma completes (φ) : ⊨ φ → ⊢ₗ φ :=
begin
  intro hm,
  sorry
end

theorem completeness (φ) : ⊢ₗ φ ↔ ⊨ φ :=
begin
  split,
  exact @sounds _,
  exact @completes _,
end

end prop