Require Import Arith.
Require Import Lia.
Require Import Nat.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example problem_31_test_case_9002 : problem_31_spec 9002 false.
Proof.
  unfold problem_31_spec.
  split.
  - intros H.
    exfalso.
    unfold IsPrime in H.
    destruct H as [_ Hdiv].
    assert (Hmod: 9002 mod 2 = 0).
    { change 9002 with (2 * 4501).
      rewrite Nat.mul_comm.
      rewrite Nat.mod_mul.
      reflexivity. }
    specialize (Hdiv 2 Hmod).
    destruct Hdiv as [H2eq1 | H2eqN]; lia.
  - intros Hfalse.
    inversion Hfalse.
Qed.