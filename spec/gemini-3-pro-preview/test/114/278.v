Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(min_total, _) :=
        fold_left (fun '(min_so_far, current_min) x =>
          let current_min' := Z.min x (current_min + x) in
          (Z.min min_so_far current_min', current_min'))
        xs (x, x)
      in min_total
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; 0%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -3%Z; 2%Z; -1%Z; 5%Z; -3%Z] = -8%Z.
Proof. reflexivity. Qed.