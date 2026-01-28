Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [-500000; 1000000; 1000000] true.
Proof.
  unfold problem_3_spec.
  split.
  - auto.
  - intros _.
    exists [-500000].
    exists [1000000; 1000000].
    split.
    + reflexivity.
    + simpl. lia.
Qed.