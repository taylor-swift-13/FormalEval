Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1%Z; -1%Z; 1%Z; -11%Z; -1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 8%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] true.
Proof.
  unfold problem_3_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    exists [1%Z; -1%Z; 1%Z; -11%Z].
    exists [-1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 8%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z].
    split.
    + reflexivity.
    + simpl. lia.
Qed.