Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  let fix aux (l : list Z) (current_sum : Z) (min_so_far : Z) : Z :=
    match l with
    | [] => min_so_far
    | x :: xs =>
      let current_sum := current_sum + x in
      let min_so_far := Z.min min_so_far current_sum in
      let current_sum := if current_sum >? 0 then 0 else current_sum in
      aux xs current_sum min_so_far
    end
  in
  match nums with
  | [] => 0
  | x :: xs =>
      let current_sum := if x >? 0 then 0 else x in
      aux xs current_sum x
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 30%Z; -1%Z; 1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 60%Z] = -2%Z.
Proof. reflexivity. Qed.