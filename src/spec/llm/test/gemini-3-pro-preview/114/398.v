Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_array_aux (l : list Z) (curr_min glob_min : Z) : Z :=
  match l with
  | [] => glob_min
  | x :: xs =>
      let new_curr := Z.min x (curr_min + x) in
      let new_glob := Z.min glob_min new_curr in
      min_sub_array_aux xs new_curr new_glob
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; 3%Z; -5%Z; 5%Z; -6%Z; 7%Z; 5%Z; -8%Z; 9%Z; 4%Z; 2%Z; 70%Z; -1%Z; 5%Z; -2%Z] = -8%Z.
Proof.
  reflexivity.
Qed.