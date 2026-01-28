Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example problem_3_test_case : problem_3_spec [-8%Z; -20%Z; 30%Z; -40%Z; 50%Z; -60%Z] true.
Proof.
  unfold problem_3_spec; simpl.
  split.
  - intros _. reflexivity.
  - intros _. exists [-8%Z]. exists [-20%Z; 30%Z; -40%Z; 50%Z; -60%Z].
    split.
    + reflexivity.
    + simpl. lia.
Qed.