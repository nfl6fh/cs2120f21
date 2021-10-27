import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
  If theres a function that maps every α value 
  that has prop p to the corresponding β value
  that has prop q, and there exists an α value
  with prop p then there must be a β value with prop q.
-/


-- Give your formal proof here
begin
  intros m n,
  cases m with atob all,
  cases n with a ahasp,
  have b := atob a,
  have ptoq := all a,
  have qfa := ptoq ahasp,
  apply exists.intro b,
  /-
  I have the necesary context here, q (atob a)
  is the same as q b, since all b is is the
  application of a to atob, I just don't know
  how to use Lean to prove this.
  -/
  admit,
end

/-
Since there exists a function f that maps all 
values a of type α that have prop p to a value
b of type β and there exists a value a of type
α, then there must exist a value b of type β
that has prop q. Since we can map all values of 
type α that have prop p to values of type β that 
have prop q, and we have a proof that such an object
of type α that has prop p exists, it follows that an
object of type β with prop q exists.
-/
