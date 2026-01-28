Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let fix aux (l : list Z) (curr_min : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | x :: xs =>
        let curr_min' := Z.min x (curr_min + x) in
        let min_so_far' := Z.min min_so_far curr_min' in
        aux xs curr_min' min_so_far'
      end
    in aux ns n n
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; 3%Z; -4%Z; 4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 10%Z; 9%Z; -10%Z; -4%Z] = -14%Z.
Proof. reflexivity. Qed.