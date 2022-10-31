import tactic data.set
import prop.language

namespace prop
open Proof

-- Łukasiewicz
inductive AxiomL : set Formula
  | P1 : ∀ {φ ψ}, AxiomL $ φ ⊃ (ψ ⊃ φ)
  | P2 : ∀ {φ ψ χ}, AxiomL $ (φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))
  | P3 : ∀ {φ ψ}, AxiomL $ (¬φ ⊃ ¬ψ) ⊃ (φ ⊃ ψ)

notation Γ `⊢ₗ` φ : 25 := Γ ⊢[AxiomL] φ
notation `⊢ₗ` φ : 25 := ∅ ⊢ₗ φ

open AxiomL
lemma reflexive_L : ∀ {Γ φ}, Γ ⊢ₗ (φ ⊃ φ) :=
begin
  intros Γ φ,
  have h₁ : (Γ ⊢ₗ (φ ⊃ ((φ ⊃ φ) ⊃ φ)) ⊃ ((φ ⊃ (φ ⊃ φ)) ⊃ (φ ⊃ φ))),
    apply in_axioms,
    apply P2,
  have h₂ : (Γ ⊢ₗ (φ ⊃ (φ ⊃ φ) ⊃ φ)),
    apply in_axioms,
    apply P1,
  have h₃ : (Γ ⊢ₗ φ ⊃ (φ ⊃ φ)),
    apply in_axioms,
    apply P1,
    
  have h₄ := @mp _ _ _ _ h₁ h₂,
  have h₅ := @mp _ _ _ _ h₄ h₃,
  assumption,
end


-- lemma append_L
--   : ∀ {Γ φ ψ}, (Γ ⊢ₗ φ) → (Γ ⊢ₗ (ψ ⊃ φ)) :=
-- begin
--   intros Γ φ ψ h,
--   have h₁ : (Γ ⊢ₗ ψ ⊃ (φ ⊃ ψ)), 
--     apply in_axioms,
--     sorry,
--   
--   -- exact h₁,
--   exact @mp AxiomL Γ φ ψ , 
-- end
lemma append_L
  : ∀ {Γ φ ψ}, (Γ ⊢ₗ ψ) → (Γ ⊢ₗ φ ⊃ ψ) := sorry

theorem deduction_L
  : ∀ {Γ φ ψ}, (Γ ∪ {φ} ⊢ₗ ψ) ↔ (Γ ⊢ₗ (φ ⊃ ψ)) :=
begin
  intros Γ φ ψ,
  split,

  generalize eq : Γ ∪ {φ} = Γ',
  intro h,
  induction h,

  case in_axioms :{
    apply in_axioms,
    sorry,
  },

  case in_context : _ _ ctx {
    rw [←eq] at ctx,
    cases ctx,
    case or.inl :{
      sorry,
    },
    case or.inr :{
      apply append_L,
      apply in_context,
      sorry,
    },
  },

  case mp: _ φ' ψ' ih₁ ih₂ {
    sorry
  },

  sorry,
end

example (φ ψ) : (⊢ₗ φ ⊃ ψ) → ({φ} ⊢ₗ ψ) := 
begin
  intro h,
  have h₃ := (iff.elim_right (@deduction_L ∅ φ ψ)) h,
  rw set.empty_union at h₃,
  exact h₃,
end

-- explosion! of law
example (φ ψ) : (⊢ₗ ¬'φ ⊃ (φ ⊃ ψ)) → ({φ, ¬'φ} ⊢ₗ ψ) :=
begin
  intro h,
  have h₁ := (iff.elim_right (@deduction_L ∅ (¬'φ) (φ ⊃ ψ))) h,
  rw set.empty_union at h₁,
  have h₂ := (iff.elim_right (@deduction_L {¬'φ} φ ψ)),
  have h₃ := h₂ h₁,
  rw set.union_def at h₃,
  sorry,
end

def consistentL := consistent AxiomL
def inconsistentL := inconsistent AxiomL

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

end prop