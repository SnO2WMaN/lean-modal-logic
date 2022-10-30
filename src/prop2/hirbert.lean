import prop2.prop 
namespace prop

inductive AxiomH : set Formula
  | A₁ : ∀ {φ ψ}, AxiomH $ φ ⊃ (ψ ⊃ φ)
  | A₂ : ∀ {φ ψ χ}, AxiomH $ (φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))
  | A₃ : ∀ {φ ψ}, AxiomH $ (¬φ ⊃ ¬ψ) ⊃ (φ ⊃ ψ)

notation Γ `⊢ₕ` φ : 25 := Γ ⊢[AxiomH] φ

lemma reflexive_H : ∀ {Γ φ}, Γ ⊢ₕ (φ ⊃ φ) :=
begin
  intros Γ φ,
  have h₁ : (Γ ⊢ₕ (φ ⊃ ((φ ⊃ φ) ⊃ φ)) ⊃ ((φ ⊃ (φ ⊃ φ)) ⊃ (φ ⊃ φ))),
    apply proof.in_axioms,
    apply AxiomH.A₂,
  have h₂ : (Γ ⊢ₕ (φ ⊃ (φ ⊃ φ) ⊃ φ)),
    apply proof.in_axioms,
    apply AxiomH.A₁,
  have h₃ : (Γ ⊢ₕ φ ⊃ (φ ⊃ φ)),
    apply proof.in_axioms,
    apply AxiomH.A₁,
    
  have h₄ := @proof.mp _ _ _ _ h₁ h₂,
  have h₅ := @proof.mp _ _ _ _ h₄ h₃,
  assumption,
end

end prop