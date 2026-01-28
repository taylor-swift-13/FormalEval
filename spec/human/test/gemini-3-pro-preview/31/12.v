Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_255379_false : problem_31_spec 255379 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime 255379 -> false = true *)
    intro H.
    destruct H as [_ Hforall].
    (* We disprove IsPrime 255379 by finding a divisor d=19 *)
    specialize (Hforall 19).
    assert (Hdiv : 255379 mod 19 = 0).
    { vm_compute. reflexivity. }
    apply Hforall in Hdiv.
    destruct Hdiv as [H1 | Hn].
    + (* Case 19 = 1 *)
      discriminate H1.
    + (* Case 19 = 255379 *)
      discriminate Hn.
  - (* Backward direction: false = true -> IsPrime 255379 *)
    intro H.
    discriminate H.
Qed.