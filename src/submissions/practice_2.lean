/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

--example : false :=     -- trick question? why?

/-
P is true if and only if P or P is true because
of the or elimination rule and the or introduction
rule.
-/

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

/-
P is true if and only if P and P are true because of the 
and elimination and introduction rules.
-/

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

/-
P or Q is true if and only if Q or P is true because
of the or symmetry rule.
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro,
  exact or.symm,
  exact or.symm,
end

/-
P and Q are true if and only if Q and P are true
because of the and symmetry rule.
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro,
  exact and.symm,
  exact and.symm,
end

/-
P and Q or R is true if and only if P and Q or P and R is true
because P is always true on both sides of the statement, and 
Q or R will always be true on the right side since either P and Q
or P and R will be true. This uses the introduction rules for and 
as well as or.
-/

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

/-
P or Q and R is true if and only if P or Q and P or R are true
because between P or Q and P or R, if P isn't true, then
Q and R both have to be true within those or statements.
This proof uses both introduction rules, similar to the above proof.
-/

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

/-
P and P or Q is true if and only if P is true
because P and anything always implies P, and P 
implies P ∧ P. This proof uses the and and or introduction
rules.
-/

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
    apply or.intro_left,
    exact p,

end

/-
P or P and Q is true if and only if P is true because
P → P and P ∧ Q → P and the other way around P → P. This 
proof uses the and and or introduction rules.
-/

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

/-
P or true is true if and only if true is true because
true will always be true, and because of the or statement
we can effectively ignore P and simplify to true → true
and this staement is true in both directions. This proof uses
the true and or introduction rules.
-/

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

/-
P or false is true if and only if P is true for a
similar reason to the above proof. Since its an or
statement we can effectively ignore false and simplify
to P → P. This proof uses the or introduction rule and 
the false elimination rule.
-/

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

/-
P and true is true if and only if P is true because 
true is always true and P always implies P. This proof
uses the and intro and true intro rules.
-/

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

/-
P and false is true if and only if false is true. I
don't 100% understand how this proof works, I just
know that lean accepted what I wrote. I don't get how
false can imply a proposition, same as true can't imply
a proposition. If its possible some clarification on this
example would greatly help me.
-/

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


