Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : Z :=
  fold_right (fun y acc => if Z.eq_dec x y then acc + 1 else acc) 0 l.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
      let fix aux (curr : Z) (rest : list Z) : Z :=
        match rest with
        | [] => curr
        | y :: ys =>
            let c_curr := count curr l in
            let c_y := count y l in
            if c_y <? c_curr then aux y ys
            else if c_y =? c_curr then
              if y <? curr then aux y ys else aux curr ys
            else aux curr ys
        end
      in aux x xs
  end.

Example test_case: solution [-1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 4%Z; 4%Z; 1%Z; 6%Z; 2%Z; -1%Z; -6%Z] = -8%Z.
Proof.
  compute. reflexivity.
Qed.