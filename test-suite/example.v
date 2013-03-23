Require Import String. 
Add Rec LoadPath "../src/" as Localize.
Add ML Path "../src/". 
Declare ML Module "localize_plugin". 

Fixpoint foo (n : nat) (b : nat) : nat :=
  match n with
    | 0 => b
    | S n => foo2 n b
  end
with foo2 (n : nat) (b : nat) : nat :=
  match n with
    | 0 => b
    | S n => foo n b
  end.

Fixpoint fact (n : nat) : nat :=
  foo n n + foo2 n n.  

Definition bar (n : nat) : nat :=
  fact (fact n).

Definition baz : nat -> nat.
  localize bar.
Defined.

Theorem baz_is_bar : forall x, baz x = bar x.
Proof.
  reflexivity.
Qed.