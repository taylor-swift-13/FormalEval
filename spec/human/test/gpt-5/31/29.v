Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example problem_31_test_case_neg_4 : problem_31_spec 4 false.
Proof.
  unfold problem_31_spec.
  split.
  - intros H.
    exfalso.
    unfold IsPrime in H.
    destruct H as [_ Hdiv].
    assert (Hmod: 4 mod 2 = 0) by reflexivity.
    specialize (Hdiv 2 Hmod).
    destruct Hdiv as [H2eq1 | H2eq4]; lia.
  - intros Hfalse.
    discriminate Hfalse.
Qed.