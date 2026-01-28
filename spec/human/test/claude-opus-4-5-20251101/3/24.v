Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Lia.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_below_zero_1 : problem_3_spec [-1%Z; -2%Z; 0%Z; 6%Z] true.
Proof.
  unfold problem_3_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    exists [-1%Z]. exists [-2%Z; 0%Z; 6%Z].
    split.
    + simpl. reflexivity.
    + simpl. lia.
Qed.