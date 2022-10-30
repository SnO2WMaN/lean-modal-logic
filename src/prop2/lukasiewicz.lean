import prop2.prop 
namespace prop

-- Łukasiewicz
inductive AxiomL : set Formula
  | P1 : ∀ {φ ψ}, AxiomL $ φ ⊃ (ψ ⊃ φ)
  | P2 : ∀ {φ ψ χ}, AxiomL $ (φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))
  | P3 : ∀ {φ ψ}, AxiomL $ (¬φ ⊃ ¬ψ) ⊃ (φ ⊃ ψ)

notation Γ `⊢ₕ` φ : 25 := Γ ⊢[AxiomL] φ

lemma reflexive_L : ∀ {Γ φ}, Γ ⊢ₕ (φ ⊃ φ) :=
begin
  intros Γ φ,
  have h₁ : (Γ ⊢ₕ (φ ⊃ ((φ ⊃ φ) ⊃ φ)) ⊃ ((φ ⊃ (φ ⊃ φ)) ⊃ (φ ⊃ φ))),
    apply proof.in_axioms,
    apply AxiomL.P2,
  have h₂ : (Γ ⊢ₕ (φ ⊃ (φ ⊃ φ) ⊃ φ)),
    apply proof.in_axioms,
    apply AxiomL.P1,
  have h₃ : (Γ ⊢ₕ φ ⊃ (φ ⊃ φ)),
    apply proof.in_axioms,
    apply AxiomL.P1,
    
  have h₄ := @proof.mp _ _ _ _ h₁ h₂,
  have h₅ := @proof.mp _ _ _ _ h₄ h₃,
  assumption,
end

theorem deduction_L (Γ : set Formula) (φ ψ : Formula) 
  : (Γ ∪ {φ} ⊢ₕ ψ) ↔ (Γ ⊢ₕ (φ ⊃ ψ)) := @deduction AxiomL _ _ _
  
end prop