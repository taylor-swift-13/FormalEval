Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
  match l with
  | [] => global_min
  | x :: xs =>
      let next_min := Z.min x (current_min + x) in
      min_sub_array_sum_aux xs next_min (Z.min global_min next_min)
  end.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux xs x x
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [-100%Z; 50%Z; -21%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; -99%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; 50%Z] = -320%Z.
Proof. reflexivity. Qed.