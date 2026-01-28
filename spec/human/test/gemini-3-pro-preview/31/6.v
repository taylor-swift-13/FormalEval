Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_4_false : problem_31_spec 4 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 4 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 4 by finding a divisor d=2 *)
    specialize (Hforall 2).
    assert (Hdiv : 4 mod 2 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H4].
    + (* Case 2 = 1 *)
      discriminate H1.
    + (* Case 2 = 4 *)
      discriminate H4.
  - (* Backward direction: false = true -> IsPrime 4 *)
    intro H.
    discriminate H.
Qed.