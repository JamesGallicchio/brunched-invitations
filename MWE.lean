
set_option hygiene false in
section

local infix:30 " ⊢ " => Entails

inductive Entails : String → String → Prop
| hi : "hi" ⊢ "hi"

end

infix:30 " ⊢ " => Entails
example : "bye" ⊢ "what" := sorry
