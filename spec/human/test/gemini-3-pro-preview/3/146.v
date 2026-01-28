Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case: problem_3_spec [100%Z; -200%Z; 300%Z; -400%Z; 500%Z; -1000%Z; 500%Z] true.
Proof.
  unfold problem_3_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    exists [100%Z; -200%Z], [300%Z; -400%Z; 500%Z; -1000%Z; 500%Z].
    split.
    + reflexivity.
    + simpl. lia.
Qed.