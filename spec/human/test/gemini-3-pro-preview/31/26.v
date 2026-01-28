Require Import ZArith.
Open Scope Z_scope.

Definition IsPrime (n : Z) : Prop :=
  1 < n /\ (forall d : Z, 0 < d -> n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : Z) : Prop := True.

Definition problem_31_spec (n : Z) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_neg1_false : problem_31_spec (-1) false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - (* Forward direction: IsPrime -1 -> false = true *)
    intro H.
    destruct H as [Hlt _].
    (* 1 < -1 is false *)
    compute in Hlt.
    discriminate Hlt.
  - (* Backward direction: false = true -> IsPrime -1 *)
    intro H.
    discriminate H.
Qed.