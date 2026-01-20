Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (res : Z) : Z :=
      match l with
      | [] => res
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let res' := Z.min res curr' in
        aux ys curr' res'
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum: min_sub_array_sum [-1; -8; 2; 4; -5; 6; 5; -4; -7; 8; 10; 8] = -11.
Proof. reflexivity. Qed.