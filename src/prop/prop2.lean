import tactic data.set
import prop.language

universe u

namespace prop

variables (A : Type u)

inductive ProofCL : set Formula
-- | ctx : ∀ {φ}, φ ∈ Γ → ProofCL φ
| P1  : ∀ {φ ψ}, ProofCL $ φ →' (ψ →' φ)
| P2  : ∀ {φ ψ χ}, ProofCL $ (φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ))
| P3  : ∀ {φ ψ}, ProofCL $ (¬'φ →' ¬'ψ) →' (ψ →' φ)
| mp  : ∀ {φ ψ}, ProofCL (φ →' ψ) → ProofCL φ → ProofCL ψ

-- notation `𝐂𝐋` := ProofCL

notation `⊢ ` φ :25 := ProofCL φ
-- notation `⊢` φ :25 := ⊢ φ

-- def consistent (Γ) : Prop := ⊥' ∉ (𝐂𝐋 Γ) 
-- def inconsistent (Γ) := ¬(consistent Γ)

open ProofCL

theorem proof_idenitity (φ) : ⊢ φ →' φ :=
begin
  have h₁ : (⊢ (φ →' ((φ →' φ) →' φ)) →' ((φ →' (φ →' φ)) →' (φ →' φ))), exact P2,
  have h₂ : (⊢ (φ →' (φ →' φ) →' φ)), exact P1,
  have h₃ : (⊢ φ →' (φ →' φ)), exact P1,
    
  have h₄ := @mp _ _ h₁ h₂,
  have h₅ := @mp _ _ h₄ h₃,
  assumption,
end

def satisfy (v : ℕ → Prop) : Formula → Prop
| (Formula.var p) := v p
| ⊥'              := false
| (φ →' ψ)        := (satisfy φ) → (satisfy ψ)

def models (v : ℕ → Prop) (φ : Formula) : Prop := satisfy v φ
infix `⊧` :25 := models

def valid (φ) := ∀ v, v ⊧ φ
prefix `⊧` :25 := valid

lemma valid_P1 (φ ψ) : ⊧ (φ →' ψ →' φ) := 
begin
  intro v,
  intros h₁ _,
  exact h₁,
end

lemma valid_P2 (φ ψ χ) : ⊧ (φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ)) := 
begin
  intro v,
  intros h₁ h₂ h₃,
  exact (h₁ h₃) (h₂ h₃),
end

lemma valid_P3 (φ ψ) : ⊧ (¬'φ →' ¬'ψ) →' (ψ →' φ) := 
begin
  intro v,
  intros h₁ h₂,
  by_contradiction h₃,
  solve_by_elim, -- TODO:
end

lemma valid_mp (φ ψ) : (⊧ φ →' ψ) → (⊧ φ) → (⊧ ψ) :=
begin
  intros h₀ h₁ v,
  exact (h₀ v) (h₁ v),
end

theorem soundness (φ) : ⊢φ → ⊧φ :=
begin
  intro h,
  induction h,
  {exact @valid_P1 _ _,},
  {exact @valid_P2 _ _ _},
  {exact @valid_P3 _ _},
  case mp: _ _ _ _ h₁ h₂ {exact @valid_mp _ _ h₁ h₂,},
end

theorem completeness (φ) : ⊧φ → ⊢φ :=
begin
  contrapose,
  intro hnP,
  sorry,
end

end prop