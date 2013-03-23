Add Rec LoadPath "../src/" as Localize.
Require Import Localize. 

Definition uni (T : Type) (n : T) : T := n.

Definition test_universe : nat * (nat -> nat) :=
  (uni _ 1, uni _ S).

Goal nat * (nat -> nat).
localize test_universe.
Defined.

Definition pair (n : nat) : nat * nat :=
  (n, S n).

Definition add_pair (n : nat) : nat :=
  let '(a,b) := pair n in
  a + b.

Definition add_pair_local : nat -> nat.
localize add_pair.
Defined.

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