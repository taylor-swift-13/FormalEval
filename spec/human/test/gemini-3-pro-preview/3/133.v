Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1%Z; 2%Z; -3%Z; 4%Z; -5%Z; 6%Z; -7%Z; 14%Z; 8%Z; -9%Z; 10%Z; -11%Z; 12%Z; 28%Z; -13%Z; 14%Z; -15%Z; -17%Z; 18%Z; -19%Z; 20%Z; -21%Z; 22%Z; -23%Z; 24%Z; -25%Z; 26%Z; -27%Z; 28%Z; -29%Z; 30%Z; -31%Z] true.
Proof.
  unfold problem_3_spec.
  split.
  - intros. reflexivity.
  - intros _.
    exists [1%Z; 2%Z; -3%Z; 4%Z; -5%Z].
    exists [6%Z; -7%Z; 14%Z; 8%Z; -9%Z; 10%Z; -11%Z; 12%Z; 28%Z; -13%Z; 14%Z; -15%Z; -17%Z; 18%Z; -19%Z; 20%Z; -21%Z; 22%Z; -23%Z; 24%Z; -25%Z; 26%Z; -27%Z; 28%Z; -29%Z; 30%Z; -31%Z].
    split.
    + reflexivity.
    + simpl. lia.
Qed.