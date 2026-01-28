Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_new: problem_3_spec [1; -1; 1; -11; -1; -1; 1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1] true.
Proof.
  unfold problem_3_spec.
  split.
  - reflexivity.
  - intros _.
    exists [1; -1; 1; -11].
    exists [-1; -1; 1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1].
    split.
    + reflexivity.
    + simpl. lia.
Qed.