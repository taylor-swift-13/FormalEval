Require Import ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition IsPrime (n : Z) : Prop :=
  1 < n /\ (forall d : Z, 0 < d -> n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : Z) : Prop := True.

Definition problem_31_spec (n : Z) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_minus_4_false : problem_31_spec (-4) false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - intro H.
    destruct H as [Hlt _].
    lia.
  - intro H.
    discriminate.
Qed.