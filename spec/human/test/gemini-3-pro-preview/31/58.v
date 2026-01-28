Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_30_false : problem_31_spec 30 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 30 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 30 by finding a divisor d=2 *)
    specialize (Hforall 2).
    assert (Hdiv : 30 mod 2 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H30].
    + (* Case 2 = 1 *)
      discriminate H1.
    + (* Case 2 = 30 *)
      discriminate H30.
  - (* Backward direction: false = true -> IsPrime 30 *)
    intro H.
    discriminate H.
Qed.