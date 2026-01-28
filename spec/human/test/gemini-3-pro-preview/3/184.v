Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1%Z; 2%Z; -4%Z; 4%Z; 25%Z; 2%Z; -2%Z; -2%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; 1%Z; -2%Z] true.
Proof.
  unfold problem_3_spec.
  split.
  - intros. reflexivity.
  - intros.
    exists [1%Z; 2%Z; -4%Z].
    exists [4%Z; 25%Z; 2%Z; -2%Z; -2%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; 1%Z; -2%Z].
    split.
    + reflexivity.
    + simpl. lia.
Qed.