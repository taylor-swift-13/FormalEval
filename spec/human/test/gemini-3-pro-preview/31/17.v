Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_40_false : problem_31_spec 40 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 40 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    specialize (Hforall 2).
    assert (Hdiv : 40 mod 2 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H40].
    + discriminate H1.
    + discriminate H40.
  - (* Backward direction: false = true -> IsPrime 40 *)
    intro H.
    discriminate H.
Qed.