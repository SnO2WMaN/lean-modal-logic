import basicmodal.language basicmodal.semantic basicmodal.syntax
import tactic

universe u 

namespace basicmodal 

variable {W : Type u}
variable 𝓕 : Kripke_Frame W  
local infix ` ≺ `:50 := 𝓕.relation

theorem completeness (φ : Formula): (𝓕 ⊧ φ) → (⊢ₖ φ) :=
begin
  sorry,
end

end basicmodal