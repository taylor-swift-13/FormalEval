Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint max_sub_array_sum_aux (l : list Z) (current_max : Z) (global_max : Z) : Z :=
  match l with
  | [] => global_max
  | x :: xs =>
      let new_current := Z.max x (current_max + x) in
      let new_global := Z.max global_max new_current in
      max_sub_array_sum_aux xs new_current new_global
  end.

Definition max_sub_array_sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => max_sub_array_sum_aux xs x x
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  let neg_nums := map Z.opp nums in
  Z.opp (max_sub_array_sum neg_nums).

Example test_minSubArraySum : minSubArraySum [1; -2; 3; -4; 5; -6; 7; -8; 9; -3; 2; -1; 5] = -8.
Proof.
  reflexivity.
Qed.