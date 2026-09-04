


Inductive foo : nat -> nat -> Type :=
  | OK : forall x, foo x (x + 1).

Inductive foo_proxy : nat -> nat -> Prop := 
  | OK1 : forall x y, foo x y -> foo_proxy x y. 

Goal (foo 1 2 /\ foo 4 5).
