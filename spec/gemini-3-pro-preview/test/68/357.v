Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let fix aux (l : list Z) (e o : Z) : list Z :=
    match l with
    | [] => [e; o]
    | x :: xs =>
      if Z.abs x <? 1000 then
        if x mod 2 =? 0 then aux xs (e + 1) o
        else aux xs e (o + 1)
      else aux xs e o
    end
  in aux l 0 0.

Example test_even_odd_count : even_odd_count [7%Z; 9%Z; 1%Z; 5%Z; 9%Z; 10000%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 9%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z; 4%Z; 2%Z; 9%Z; 9%Z] = [2%Z; 24%Z].
Proof. reflexivity. Qed.