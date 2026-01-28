Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example problem_3_test_nonempty : problem_3_spec [-1%Z; -3%Z; 0%Z; 6%Z; 9%Z] true.
Proof.
  unfold problem_3_spec; simpl.
  split.
  - intros _. reflexivity.
  - intros _. exists [-1%Z]. exists [-3%Z; 0%Z; 6%Z; 9%Z]. split.
    + simpl. reflexivity.
    + simpl. lia.
Qed.