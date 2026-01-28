Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example problem_31_test_case_77 : problem_31_spec 77 false.
Proof.
  unfold problem_31_spec.
  split.
  - intros H.
    exfalso.
    unfold IsPrime in H.
    destruct H as [_ Hdiv].
    assert (Hmod: 77 mod 7 = 0) by reflexivity.
    specialize (Hdiv 7 Hmod).
    destruct Hdiv as [H7eq1 | H7eq77]; lia.
  - intros Hfalse.
    discriminate Hfalse.
Qed.