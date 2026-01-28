Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_57_false : problem_31_spec 57 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 57 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 57 by finding a divisor d=3 *)
    specialize (Hforall 3).
    assert (Hdiv : 57 mod 3 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H57].
    + (* Case 3 = 1 *)
      discriminate H1.
    + (* Case 3 = 57 *)
      discriminate H57.
  - (* Backward direction: false = true -> IsPrime 57 *)
    intro H.
    discriminate H.
Qed.