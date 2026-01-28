Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
    let current_min' := Z.min x (current_min + x) in
    let min_so_far' := Z.min min_so_far current_min' in
    min_sub_array_sum_aux xs current_min' min_so_far'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-100; -10; -50; 100; 50; -50; 100; -100; 100; 99; -100; 50; -50; 100; -100; -100000; 50; -51; 100; -100] = -100101.
Proof. reflexivity. Qed.