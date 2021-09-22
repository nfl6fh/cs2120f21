/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

--example : false :=     -- trick question? why?

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro,
    assume pandp,
    apply and.elim pandp,
      assume p p,
      exact p,
    assume p,
    apply and.intro,
      exact p,
      exact p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro,
  exact or.symm,
  exact or.symm,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro,
  exact and.symm,
  exact and.symm,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
    assume p,
    cases p,
    cases p_right,
    apply or.intro_left,
    apply and.intro,
    exact p_left,
    exact p_right,
    apply or.intro_right,
    apply and.intro,
    exact p_left,
    exact p_right,
    assume p,
    cases p,
    cases p,
    apply and.intro,
    exact p_left,
    apply or.intro_left,
    exact p_right,
    cases p,
    apply and.intro,
    exact p_left,
    apply or.intro_right,
    exact p_right,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
    assume p,
    cases p,
    apply and.intro,
    apply or.intro_left,
    exact p,
    apply or.intro_left,
    exact p,
    apply and.intro,
    cases p,
    apply or.intro_right,
    exact p_left,
    cases p,
    apply or.intro_right,
    exact p_right,
    assume p,
    cases p,
    cases p_left,
    apply or.intro_left,
    exact p_left,
    cases p_right,
    apply or.intro_left,
    exact p_right,
    apply or.intro_right,
    apply and.intro,
    exact p_left,
    exact p_right,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
    assume p,
    cases p,
    exact p_left,
    assume p,
    apply and.intro,
    exact p,
    exact or.intro_left Q p,

end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
    assume p,
    cases p,
    exact p,
    exact and.left p,
    assume p,
    apply or.intro_left,
    exact p, 
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
    assume p,
    exact true.intro,
    assume p,
    apply or.intro_right,
    exact true.intro,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
    assume p,
    cases p,
    exact p,
    apply false.elim,
    exact p,
    assume p,
    apply or.intro_left,
    exact p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
    exact and.left,
    assume p,
    apply and.intro,
    exact p,
    exact true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
    exact and.right,
    assume p,
    apply and.intro,
    apply false.elim,
    exact p,
    exact p,
end


