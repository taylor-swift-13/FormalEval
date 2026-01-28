Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_1234564_false : problem_31_spec 1234564 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 1234564 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 1234564 by finding a divisor d=2 *)
    specialize (Hforall 2).
    assert (Hdiv : 1234564 mod 2 = 0).
    { reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | Hn].
    + (* Case 2 = 1 *)
      discriminate H1.
    + (* Case 2 = 1234564 *)
      discriminate Hn.
  - (* Backward direction: false = true -> IsPrime 1234564 *)
    intro H.
    discriminate H.
Qed.