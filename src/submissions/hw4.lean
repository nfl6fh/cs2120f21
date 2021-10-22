-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have zero := eq.refl 0,
  contradiction,
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp,
  assumption,
  contradiction,
end

-- 5
/-
This, along with a couple of other problems I know how to logically
explain, however I do not know how to prove them using lean. For
this one ¬(P ∧ Q) implies ¬P ∨ ¬Q because if P ∧ Q is false,
either P or Q has to be false. Inversely, if either P or Q is false,
then P and Q is a false statement.
-/
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,
  assume h,
  have pornp := classical.em P,
  cases pornp,
  have qornq := classical.em Q,
  cases qornq,
  have pandq := and.intro pornp qornq,
  contradiction,
  apply or.inr,
  exact qornq,
  apply or.inl,
  exact pornp,
  admit,
end


-- 6
/-
This is another one that I understand logically but do not understand
lean enough to write the formal proof. ¬(P ∨ Q) implies ¬P ∧ ¬Q because
if (P ∨ Q) is false, both P and Q must be false. Inversely, if ¬P ∧ ¬Q
then neither P nor Q are true so P ∨ Q would be false.
-/
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q p,
  have pornp := classical.em P,
  cases pornp,
  have qornq := classical.em Q,
  cases qornq,
  have porq := or.intro_left Q pornp,
  contradiction,
  have porq := or.intro_left Q pornp,
  contradiction,
  have qornq := classical.em Q,
  cases qornq,
  have porq := or.intro_left P qornq,
  have qorp := or.symm porq,
  contradiction,
  apply and.intro,
  exact pornp,
  exact qornq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  assume p,
  cases p,
  apply or.inl,
  exact p,
  cases p,
  apply or.inr,
  exact p_right,
  assume p,
  cases p,
  apply or.inl,
  exact p,
  have pornp := classical.em P,
  cases pornp,
  apply or.inl,
  exact pornp,
  apply or.inr,
  apply and.intro,
  exact pornp,
  exact p,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  assume p,
  cases p,
  cases p_left,
  apply or.inl,
  exact p_left,
  cases p_right,
  apply or.inl,
  exact p_right,
  apply or.inr,
  apply and.intro,
  exact p_left,
  exact p_right,
  assume p,
  apply and.intro,
  cases p,
  apply or.inl,
  exact p,
  apply or.inr,
  cases p,
  exact p_left,
  cases p,
  apply or.inl,
  exact p,
  apply or.inr,
  cases p,
  exact p_right,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  assume p,
  cases p,
  cases p_left,
  cases p_right,
  apply or.inl,
  apply and.intro,
  exact p_left,
  exact p_right,
  apply or.inr,
  apply or.inl,
  apply and.intro,
  exact p_left,
  exact p_right,
  cases p_right,
  apply or.inr,
  apply or.inr,
  apply or.inl,
  apply and.intro,
  exact p_left,
  exact p_right,
  apply or.inr,
  apply or.inr,
  apply or.inr,
  apply and.intro,
  exact p_left,
  exact p_right,
  assume p,
  cases p,
  apply and.intro,
  apply or.inl,
  cases p,
  exact p_left,
  apply or.inl,
  cases p,
  exact p_right,
  cases p,
  apply and.intro,
  apply or.inl,
  cases p,
  exact p_left,
  apply or.inr,
  cases p,
  exact p_right,
  cases p,
  apply and.intro,
  apply or.inr,
  cases p,
  exact p_left,
  apply or.inl,
  cases p,
  exact p_right,
  apply and.intro,
  apply or.inr,
  cases p,
  exact p_left,
  apply or.inr,
  cases p,
  exact p_right,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
/-
This is another one I'm not sure how to formally prove, I've attempted
to use the witness of 5 as a natural number that isn't 0, but don't
know how to prove this using lean. 
-/
lemma not_all_nats_are_zero : ∃(n : ℕ), (n ≠ 0) :=
begin
  apply exists.intro 5,
  trivial,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,
  assume p,
  have pornp := classical.em P,
  cases pornp,
  apply or.inr,
  exact p pornp,
  apply or.inl,
  exact pornp,
  assume p,
  cases p,
  contradiction,
  assume h,
  exact p,
end

-- 12
/-
This is another one that I get, but cannot prove with lean. If P implies
Q, then ¬Q implies ¬P. If P is true, Q will also be true, thus, if Q is
false, P cannot be true because if P were true then Q would also be true.
-/
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q p,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp,
  cases qornq,
  assume h,
  contradiction,
  assume h,

end

-- 13
/-
This is simply the inverse of the above proof. If ¬P implies ¬Q, then 
Q implies P. If P is false, Q will also be false, thus, if Q is true,
P must also be true because if it were false it would imply that Q was
false.
-/
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q p,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp,
  cases qornq,
  assume h,
  exact pornp,
  assume h,
  exact pornp,
  assume h,

end

