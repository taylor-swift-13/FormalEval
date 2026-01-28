Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ (fold_left Z.add prefix 0 < 0 <-> output = true)).

Example test_problem_3_15_2_3_neg6 : problem_3_spec [15%Z; 2%Z; 3%Z; -6%Z] false.
Proof.
  unfold problem_3_spec.
  exists (@nil Z), [15%Z; 2%Z; 3%Z; -6%Z].
  split.
  - simpl. reflexivity.
  - simpl. split.
    + intro H. exfalso. lia.
    + intro H. exfalso. discriminate H.
Qed.