Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1; -2; 3; -4; 5; -6; 7; -8; 9; -10] true.
Proof.
  unfold problem_3_spec.
  split.
  - (* Forward direction: (exists ...) -> true = true *)
    intros. reflexivity.
  - (* Backward direction: true = true -> (exists ...) *)
    intros _.
    (* We need to find a prefix with sum < 0.
       Prefix [1; -2] sums to -1 < 0. *)
    exists [1; -2].
    exists [3; -4; 5; -6; 7; -8; 9; -10].
    split.
    + (* Check concatenation *)
      reflexivity.
    + (* Check sum < 0 *)
      simpl. lia.
Qed.