Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [-20; -10; 1; 2; -3; 4; -5; 6; -7; 8; 20; -29; -11; 12; -500000; -13; 14; -15; 16; -17; 18; -19; 20; -21; 22; -23; 24; -25; 26; -27; 25; 28; -29; 30; -9] true.
Proof.
  unfold problem_3_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    exists [-20].
    exists [-10; 1; 2; -3; 4; -5; 6; -7; 8; 20; -29; -11; 12; -500000; -13; 14; -15; 16; -17; 18; -19; 20; -21; 22; -23; 24; -25; 26; -27; 25; 28; -29; 30; -9].
    split.
    + reflexivity.
    + simpl. lia.
Qed.