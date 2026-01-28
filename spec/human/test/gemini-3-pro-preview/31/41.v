Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_35_false : problem_31_spec 35 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 35 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 35 by finding a divisor d=5 *)
    specialize (Hforall 5).
    assert (Hdiv : 35 mod 5 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H35].
    + (* Case 5 = 1 *)
      discriminate H1.
    + (* Case 5 = 35 *)
      discriminate H35.
  - (* Backward direction: false = true -> IsPrime 35 *)
    intro H.
    discriminate H.
Qed.