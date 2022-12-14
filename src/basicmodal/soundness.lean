import basicmodal.language basicmodal.semantic basicmodal.syntax
import tactic

universe u 

namespace basicmodal 

variable {W : Type u}
variable ð : Kripke_Frame W  
local infix ` âº `:50 := ð.relation

lemma P1_soundness (Ï Ï)
  : ð â§ (Ï â' (Ï â' Ï)) :=
begin
  intros v w,
  sorry,
end

lemma P2_soundness (Ï Ï Ï)
  : ð â§ (Ï â' (Ï â' Ï)) â' ((Ï â' Ï) â' (Ï â' Ï)) :=
begin
  intros v w,

  sorry,
end

lemma P3_soundness (Ï Ï)
  : ð â§ (Â¬'Ï â' Â¬'Ï) â' (Ï â' Ï) :=
begin
  intros v w,
  sorry,
end

lemma K_soundness (Ï Ï)
  : ð â§ â¡(Ï â' Ï) â' (â¡Ï â' Ï) :=
begin 
  intros v w h hâ, 
  sorry,
end

lemma mp_soundness (Ï Ï)
  : (ð â§ Ï â' Ï) â (ð â§ Ï) â (ð â§ Ï) :=
begin
  tauto,
end
  
lemma nec_soundness (Ï)
  : (ð â§ Ï) â (ð â§ â¡Ï) := 
begin
  tauto,
end

theorem soundness  (Ï : Formula): (â¢â Ï) â (ð â§ Ï) :=
begin
  assume h,
  induction h, 
  case P1: { exact @P1_soundness _ _ _ _},
  case P2: {exact @P2_soundness _ _ _ _ _},
  case P3: {exact @P3_soundness _ _ _ _},
  case K: { exact @K_soundness _ _ _ _,},
  case mp: _ _ _ _ hâ hâ { exact mp_soundness _ _ _ hâ hâ, },
  case nec: _ _ hâ { exact nec_soundness _ _ hâ, },
end

end basicmodal