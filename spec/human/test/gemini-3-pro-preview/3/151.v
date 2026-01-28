Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1; 2; 3; 4; 5; -15; 6; 8; 8; 9; -19; 21; -19; -19] true.
Proof.
  unfold problem_3_spec.
  split.
  - intros. reflexivity.
  - intros.
    exists [1; 2; 3; 4; 5; -15; 6; 8; 8; 9; -19; 21; -19; -19], [].
    split.
    + rewrite app_nil_r. reflexivity.
    + simpl. lia.
Qed.