Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [2%Z; -20%Z; 3%Z; 4%Z; 5%Z; -15%Z; 8%Z; 8%Z; 9%Z; -19%Z; 21%Z; -19%Z] true.
Proof.
  unfold problem_3_spec.
  split.
  - intros. reflexivity.
  - intros _.
    exists [2; -20]%Z.
    exists [3; 4; 5; -15; 8; 8; 9; -19; 21; -19]%Z.
    split.
    + reflexivity.
    + simpl. lia.
Qed.