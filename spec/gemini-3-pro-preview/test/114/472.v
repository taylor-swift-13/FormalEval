Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (min_sf : Z) : Z :=
      match l with
      | [] => min_sf
      | y :: ys =>
        let new_curr := Z.min y (curr + y) in
        let new_min_sf := Z.min min_sf new_curr in
        aux ys new_curr new_min_sf
      end
    in aux xs x x
  end.

Example check : minSubArraySum [100000%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; 4%Z; -3%Z; -1%Z; 4%Z] = -8%Z.
Proof.
  reflexivity.
Qed.