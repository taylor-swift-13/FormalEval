Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_sum : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let new_current := current_sum + x in
      let new_min := Z.min min_so_far new_current in
      let reset_current := if new_current >? 0 then 0 else new_current in
      minSubArraySum_aux xs reset_current new_min
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux nums 0 x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; 0%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -100%Z; -1%Z; 1%Z; -50%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -150%Z.
Proof. reflexivity. Qed.