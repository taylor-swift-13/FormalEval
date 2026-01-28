Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_1_false : problem_31_spec 1 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - intro H.
    destruct H as [H1 _].
    apply Nat.lt_irrefl in H1.
    contradiction.
  - intro H.
    discriminate H.
Qed.