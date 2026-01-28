Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_85_false : problem_31_spec 85 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 85 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 85 by finding a divisor d=5 *)
    specialize (Hforall 5).
    assert (Hdiv : 85 mod 5 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H85].
    + (* Case 5 = 1 *)
      discriminate H1.
    + (* Case 5 = 85 *)
      discriminate H85.
  - (* Backward direction: false = true -> IsPrime 85 *)
    intro H.
    discriminate H.
Qed.