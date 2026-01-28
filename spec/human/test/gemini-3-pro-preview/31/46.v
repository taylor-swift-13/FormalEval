Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_1011_false : problem_31_spec 1011 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 1011 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 1011 by finding a divisor d=3 *)
    specialize (Hforall 3).
    assert (Hdiv : 1011 mod 3 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H1011].
    + (* Case 3 = 1 *)
      discriminate H1.
    + (* Case 3 = 1011 *)
      discriminate H1011.
  - (* Backward direction: false = true -> IsPrime 1011 *)
    intro H.
    discriminate H.
Qed.