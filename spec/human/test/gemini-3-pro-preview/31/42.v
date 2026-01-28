Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_64_false : problem_31_spec 64 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 64 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 64 by finding a divisor d=2 *)
    specialize (Hforall 2).
    assert (Hdiv : 64 mod 2 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H64].
    + (* Case 2 = 1 *)
      discriminate H1.
    + (* Case 2 = 64 *)
      discriminate H64.
  - (* Backward direction: false = true -> IsPrime 64 *)
    intro H.
    discriminate H.
Qed.