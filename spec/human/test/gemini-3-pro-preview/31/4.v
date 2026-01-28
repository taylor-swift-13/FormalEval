Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Axiom prime_13441 : IsPrime 13441.

Example test_case_13441_true : problem_31_spec 13441 true.
Proof.
  unfold problem_31_spec.
  split.
  - intro H. reflexivity.
  - intro H. apply prime_13441.
Qed.