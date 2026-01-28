Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let aux (acc : Z * Z) (n : Z) :=
        let (curr_min, min_so_far) := acc in
        let curr_min' := Z.min n (curr_min + n) in
        (curr_min', Z.min min_so_far curr_min')
      in
      snd (fold_left aux xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -29%Z; 3%Z; 4%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z] = -29%Z.
Proof. reflexivity. Qed.