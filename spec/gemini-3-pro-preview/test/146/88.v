Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition move_one_ball (arr : list Z) : Z :=
  match arr with
  | [] => 1
  | x :: xs =>
      let fix count_drops (prev : Z) (l : list Z) : Z :=
        match l with
        | [] => 0
        | y :: ys => (if prev >? y then 1 else 0) + count_drops y ys
        end
      in
      let drops := count_drops x xs in
      let last_elem := last xs x in
      let final_drop := if last_elem >? x then 1 else 0 in
      if drops + final_drop <=? 1 then 1 else 0
  end.

Example test_move_one_ball: move_one_ball [14%Z; -8%Z; 62%Z; -18%Z; 6%Z; -76%Z; 6%Z; 5%Z] = 0%Z.
Proof. reflexivity. Qed.