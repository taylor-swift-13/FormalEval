Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_6_false : problem_31_spec 6 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 6 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 6 by finding a divisor d=2 *)
    specialize (Hforall 2).
    assert (Hdiv : 6 mod 2 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H6].
    + (* Case 2 = 1 *)
      discriminate H1.
    + (* Case 2 = 6 *)
      discriminate H6.
  - (* Backward direction: false = true -> IsPrime 6 *)
    intro H.
    discriminate H.
Qed.