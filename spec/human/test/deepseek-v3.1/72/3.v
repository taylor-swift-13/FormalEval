Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left Z.add q 0 <= w)).

Example test_case_1 : problem_72_spec [3; 2; 3] 9 true.
Proof.
  unfold problem_72_spec.
  split.
  - intros H.
    split.
    + simpl.
      reflexivity.
    + simpl.
      lia.
  - intros [H1 H2].
    reflexivity.
Qed.

Example test_case_2 : problem_72_spec [3] 5 true.
Proof.
  unfold problem_72_spec.
  split.
  - intros H.
    split.
    + simpl.
      reflexivity.
    + simpl.
      lia.
  - intros [H1 H2].
    reflexivity.
Qed.