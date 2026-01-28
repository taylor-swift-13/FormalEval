Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_non_empty_list : problem_8_spec [2; 13; 7; 11; 13; 49] 95 1275274.
Proof.
  unfold problem_8_spec.
  split.
  - unfold fold_left. simpl. reflexivity.
  - unfold fold_left. simpl. reflexivity.
Qed.