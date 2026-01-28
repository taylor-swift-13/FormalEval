Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example problem_3_test_empty : problem_3_spec [0%Z; 0%Z; 0%Z; 0%Z; -1%Z] true.
Proof.
  unfold problem_3_spec; simpl.
  split.
  - intros _. reflexivity.
  - intros _. exists [0%Z; 0%Z; 0%Z; 0%Z; -1%Z]. exists [].
    split.
    + simpl. reflexivity.
    + simpl. lia.
Qed.