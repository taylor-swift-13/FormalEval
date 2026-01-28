Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_33_false : problem_31_spec 33 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 33 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 33 by finding a divisor d=3 *)
    specialize (Hforall 3).
    assert (Hdiv : 33 mod 3 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H33].
    + (* Case 3 = 1 *)
      discriminate H1.
    + (* Case 3 = 33 *)
      discriminate H33.
  - (* Backward direction: false = true -> IsPrime 33 *)
    intro H.
    discriminate H.
Qed.