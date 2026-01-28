Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_1234568_false : problem_31_spec 1234568 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - intro H.
    destruct H as [_ Hforall].
    specialize (Hforall 2).
    assert (Hdiv : 1234568 mod 2 = 0).
    { vm_compute. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H2].
    + discriminate H1.
    + discriminate H2.
  - intro H.
    discriminate H.
Qed.