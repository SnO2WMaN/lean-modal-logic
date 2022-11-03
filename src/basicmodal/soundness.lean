import basicmodal.language basicmodal.semantic basicmodal.syntax
import tactic

universe u 

namespace basicmodal 

variable {W : Type u}
variable 𝓕 : Kripke_Frame W  
local infix ` ≺ `:50 := 𝓕.relation

lemma P1_soundness (φ ψ)
  : 𝓕 ⊧ (φ →' (ψ →' φ)) :=
begin
  intros v w,
  sorry,
end

lemma P2_soundness (φ ψ χ)
  : 𝓕 ⊧ (φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ)) :=
begin
  intros v w,

  sorry,
end

lemma P3_soundness (φ ψ)
  : 𝓕 ⊧ (¬'φ →' ¬'ψ) →' (φ →' ψ) :=
begin
  intros v w,
  sorry,
end

lemma K_soundness (φ ψ)
  : 𝓕 ⊧ □(φ →' ψ) →' (□φ →' ψ) :=
begin 
  intros v w h h₀, 
  sorry,
end

lemma mp_soundness (φ ψ)
  : (𝓕 ⊧ φ →' ψ) → (𝓕 ⊧ φ) → (𝓕 ⊧ ψ) :=
begin
  tauto,
end
  
lemma nec_soundness (φ)
  : (𝓕 ⊧ φ) → (𝓕 ⊧ □φ) := 
begin
  tauto,
end

theorem soundness  (φ : Formula): (⊢ₖ φ) → (𝓕 ⊧ φ) :=
begin
  assume h,
  induction h, 
  case P1: { exact @P1_soundness _ _ _ _},
  case P2: {exact @P2_soundness _ _ _ _ _},
  case P3: {exact @P3_soundness _ _ _ _},
  case K: { exact @K_soundness _ _ _ _,},
  case mp: _ _ _ _ h₀ h₁ { exact mp_soundness _ _ _ h₀ h₁, },
  case nec: _ _ h₀ { exact nec_soundness _ _ h₀, },
end

end basicmodal