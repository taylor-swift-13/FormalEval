Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let fix aux (xs : list Z) (e o : Z) : list Z :=
    match xs with
    | [] => [e; o]
    | x :: rest =>
      if andb (Z.even x) (x <? 10) then aux rest (e + 1) o
      else if andb (Z.odd x) (x <? 5) then aux rest e (o + 1)
      else aux rest e o
    end
  in aux l 0 0.

Example test_even_odd_count: even_odd_count [2%Z; 5%Z; 11%Z; 7%Z; 16%Z; 11%Z; 2%Z; 9%Z; 9%Z; 11%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.