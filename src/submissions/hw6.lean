import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/

example: ∀ {α : Type} {L : set α}, L ∩ L = L :=
begin
  assume a b,
  apply set.ext,
  assume c,
  split,
  assume d,
  cases d,
  exact d_left,
  assume e,
  apply and.intro,
  exact e,
  exact e,
end


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

example: ∀ {α : Type} {L R : set α}, L ∪ R = R ∪ L :=
begin
  intros α L R,
  apply set.ext,
  assume a,
  split,
  assume m,
  cases m,
  apply or.intro_right,
  exact m,
  apply or.inl,
  exact m,
  assume j,
  cases j,
  apply or.inr,
  exact j,
  apply or.inl,
  exact j,
end

/-
The union of two sets is the set that contains the elements
that are in one or both of the sets. As a result of this, the
order that the sets are in doesn't matter. 
Ex.
A = {1,2,3}
B = {3,4,5}

A ∪ B = {1,2,3,4,5}
B ∪ A = {3,4,5,1,2}

-/

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

example: ∀ {α : Type} {S L R : set α}, S ⊆ L → L ⊆ R → S ⊆ R :=
begin
  intros α S L R,
  assume m n,
  apply trans m n,
end

/-
If S is a subset of L and L is a subset of R,
then S is also a subset of R. Every object that 
exists in set S will also exist in set L because
of the definition of a subset, and this is also
true for every element in set L will exist in set R.

I don't beleive that the subset operator is reflexive
since {1,2,3} is a subset of {1,2,3,4,5} but {1,2,3,4,5}
is not a subset of {1,2,3}.
-/

/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

example: ∀ {α : Type} {S L R : set α}, (S ∪ L) ∪ R = S ∪ (L ∪ R) :=
begin
  intros α S L R,
  apply set.ext,
  assume a,
  split,
  assume h,
  cases h,
  cases h,
  apply or.inl,
  assumption,
  apply or.inr,
  apply or.inl,
  assumption,
  apply or.inr,
  apply or.inr,
  assumption,
  
  assume h,
  cases h,
  apply or.inl,
  apply or.inl,
  assumption,
  cases h,
  apply or.inl,
  apply or.inr,
  assumption,
  apply or.inr,
  assumption,
end

/-
The union operator is associative as an extesion of the commutative
nature of this operator, thus, since the order doesn't matter, 
the parenthesis are effectively useless.
-/

example: ∀ {α : Type} {S L R : set α}, (S ∩ L) ∩ R = S ∩ (L ∩ R) :=
begin
  intros α S L R,
  apply set.ext,
  assume a,
  split,
  assume h,
  cases h,
  cases h_left,
  apply and.intro,
  assumption,
  apply and.intro,
  assumption,
  assumption,
  
  assume h,
  cases h,
  cases h_right,
  apply and.intro,
  apply and.intro,
  assumption,
  assumption,
  assumption,
end

/-
The union and intersecton operators are associative as an extesion 
of the commutative nature of these operators, thus, since the order 
doesn't matter, the parenthesis are effectively useless.
-/

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/

example: ∀ {α : Type} {S L R : set α}, S ∩ (L ∩ R) = S ∩ L ∩ S ∩ R :=
begin 
  intros α S L R,
  apply set.ext,
  assume a,
  split,
  assume h,
  cases h,
  cases h_right,
  apply and.intro,
  apply and.intro,
  apply and.intro,
  assumption,
  assumption,
  assumption,
  assumption,

  assume h,
  cases h,
  cases h_left,
  cases h_left_left,
  apply and.intro,
  exact h_left_right,
  apply and.intro,
  assumption,
  assumption,
end

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

example: ∀ {α : Type} {S L R : set α}, S ∪ (L ∩ R) = (S ∪ L) ∩ (S ∪ R) :=
begin
  intros α S L R,
  apply set.ext,
  assume a,
  split,
  assume h,
  cases h,
  apply and.intro,
  apply or.inl,
  assumption,
  apply or.inl,
  assumption,
  cases h,
  apply and.intro,
  apply or.inr,
  assumption,
  apply or.inr,
  assumption,
  
  assume h,
  cases h,
  cases h_left,
  apply or.inl,
  assumption,
  cases h_right,
  apply or.inl,
  assumption,
  apply or.inr,
  apply and.intro,
  assumption,
  assumption,
end

