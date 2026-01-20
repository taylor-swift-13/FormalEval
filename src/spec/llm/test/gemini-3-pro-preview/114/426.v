Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
  match l with
  | [] => global_min
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min global_min new_current in
      min_sub_array_sum_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [10%Z; -20%Z; 30%Z; -40%Z; 50%Z; 1%Z; 101%Z; 70%Z; -80%Z; 3%Z; 90%Z; -100%Z; 50%Z] = -100%Z.
Proof. reflexivity. Qed.