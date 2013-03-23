Require Import String. 
Add Rec LoadPath "../src/" as Localize.
Add ML Path "../src/". 
Declare ML Module "localize_plugin". 

Definition foo (n : nat) : nat :=
  n + 1 - 3.

Definition bar (n : nat) : nat :=
  foo (foo n).

Definition baz : nat -> nat.
  localize bar blacklist [ foo ].
Defined.

Theorem baz_is_bar : forall x, baz x = bar x.
Proof.
  reflexivity.
Qed.