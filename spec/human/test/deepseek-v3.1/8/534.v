Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_empty_list : problem_8_spec [2%Z; -9%Z; 10%Z; 2%Z; -4%Z; 3%Z; -5%Z; 3%Z; 0%Z; -8%Z; -6%Z; -4%Z; -4%Z; -5%Z] (-25) 0.
Proof.
  unfold problem_8_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.