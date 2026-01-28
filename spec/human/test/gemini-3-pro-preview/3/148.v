Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case: problem_3_spec [-5; -10; -15; -20; 30; -1000; 50; 100; -1000] true.
Proof.
  unfold problem_3_spec.
  split.
  - intros. reflexivity.
  - intros _.
    exists [-5], [-10; -15; -20; 30; -1000; 50; 100; -1000].
    split.
    + reflexivity.
    + simpl. lia.
Qed.