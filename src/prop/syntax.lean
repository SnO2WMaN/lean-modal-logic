import prop.language 

universe u

namespace prop

@[reducible] def context (A : Type u) := set (formula A) 
notation (name := context.plus) Γ `∪` φ := set.insert φ Γ

variables (A : Type u)

inductive proof : context A → formula A → Type u
  | in_context : ∀ {Γ φ} {h : φ ∈ Γ}, proof Γ φ
  -- | verum : ∀ {Γ}, proof Γ ⊤
  | A₁ : ∀ {Γ φ ψ}, proof Γ (φ ⊃ (ψ ⊃ φ))
  | A₂ : ∀ {Γ φ ψ χ}, proof Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
  | A₃ : ∀ {Γ φ ψ}, proof Γ ((¬φ ⊃ ¬ψ) ⊃ (φ ⊃ ψ))
  | mp : ∀ {Γ φ ψ} 
    {hpq: proof Γ (φ ⊃ ψ)} 
    {hp: proof Γ φ}, 
    proof Γ ψ

def provable (Γ : context A) (φ : formula A) : Prop := nonempty (proof A Γ φ)

variables (Γ : context A) (φ : formula A)

lemma identify : ∀ {Γ φ}, provable A Γ (φ ⊃ φ) :=
begin
  intros Γ φ,
  have h1 := φ ⊃ φ,
  sorry
end

end prop