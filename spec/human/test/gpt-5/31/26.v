Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition IsPrime (n : Z) : Prop :=
  1 < n /\ (forall d : Z, d <> 0 -> n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : Z) : Prop := True.

Definition problem_31_spec (n : Z) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example problem_31_test_case_neg1 : problem_31_spec (-1%Z) false.
Proof.
  unfold problem_31_spec.
  split.
  - intros H.
    destruct H as [Hlt _].
    lia.
  - intros Hfalse.
    discriminate Hfalse.
Qed.