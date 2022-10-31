import tactic data.set
import prop.language prop.semantics prop.syntax
 
namespace prop
  
def consistentL := consistent AxiomL
def inconsistentL := inconsistent AxiomL

def soundness (AX : set Formula) := ∀ {Γ φ}, (Γ ⊢[AX] φ) → (Γ ⊨ φ)
def completeness (AX : set Formula) := ∀ {Γ φ}, (Γ ⊨ φ) → (Γ ⊢[AX] φ)

lemma lemma_2_10 (Γ φ) : (Γ ⊢ₗ φ) → (Γ ⊢ₗ ¬'φ) → consistentL Γ :=
begin
  intros ht hf,
  sorry,
end

lemma lemma_2_10' (Γ φ) : inconsistentL Γ → ((Γ ⊢ₗ φ) ∨ (Γ ⊢ₗ ¬'φ)) :=
begin
  sorry,
end

lemma lemma_2_11 (Γ φ) : consistentL (Γ ∩ {φ}) → (Γ ⊢ₗ φ) := 
begin
  intro h,
  sorry 
end

lemma lemma_2_12 (Γ φ) : inconsistentL Γ → (inconsistentL (Γ ∪ {φ})) ∨ (inconsistentL (Γ ∪ {φ})) :=
begin
  sorry
end

theorem soundness_L : soundness AxiomL :=
begin
  intros Γ φ,
  intro he,
  induction he,
  
  case in_axioms :{
    sorry,
  },

  case in_context :{
    sorry,
  },

  case mp :{
    sorry,
  },
end

theorem completeness_L : completeness AxiomL :=
begin
  intros Γ φ,
  intro hm,
  sorry
end

end prop