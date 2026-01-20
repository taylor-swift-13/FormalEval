Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
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
  | x :: xs =>
      let s := x in
      let min_s := x in
      let s' := if s >? 0 then 0 else s in
      minSubArraySum_aux xs s' min_s
  end.

Example test_minSubArraySum : minSubArraySum [10%Z; -20%Z; 30%Z; -40%Z; 3%Z; 50%Z; -60%Z; 70%Z; -80%Z; -100%Z; 10%Z] = -180%Z.
Proof. reflexivity. Qed.