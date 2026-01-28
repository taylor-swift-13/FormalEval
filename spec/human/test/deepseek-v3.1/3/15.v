Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_non_empty_list : problem_3_spec [10; -15; 20; -25; 30; -35; 40; -45] true.
Proof.
  unfold problem_3_spec.
  split.
  - intro H.
    reflexivity.
  - intro H.
    exists [10; -15].
    exists [20; -25; 30; -35; 40; -45].
    split.
    + reflexivity.
    + simpl.
      lia.
Qed.