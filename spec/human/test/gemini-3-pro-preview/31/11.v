Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_77_false : problem_31_spec 77 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 77 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 77 by finding a divisor d=7 *)
    specialize (Hforall 7).
    assert (Hdiv : 77 mod 7 = 0).
    { simpl. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | H77].
    + (* Case 7 = 1 *)
      discriminate H1.
    + (* Case 7 = 77 *)
      discriminate H77.
  - (* Backward direction: false = true -> IsPrime 77 *)
    intro H.
    discriminate H.
Qed.