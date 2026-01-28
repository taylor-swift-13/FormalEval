Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_non_empty_list : problem_3_spec [-1%Z; -3%Z; 6%Z; -3%Z] true.
Proof.
  unfold problem_3_spec.
  split.
  - intro H.
    reflexivity.
  - intro H.
    exists [-1%Z].
    exists [-3%Z; 6%Z; -3%Z].
    split.
    + reflexivity.
    + simpl.
      lia.
Qed.