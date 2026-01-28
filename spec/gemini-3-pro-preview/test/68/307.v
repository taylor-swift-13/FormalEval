Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let fix aux (l : list Z) (e o : Z) : list Z :=
    match l with
    | [] => [e; o]
    | x :: xs =>
      if Z.eqb x 0 then [e; o]
      else if Z.even x then aux xs (e + 1) o
      else aux xs e (o + 1)
    end
  in aux l 0 0.

Example test_case: even_odd_count [0%Z; 17%Z; 2%Z; 3%Z; 6%Z; 9%Z; 8%Z; 1%Z; 3%Z; 13%Z; 7%Z; 9%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 29%Z; 36%Z; 31%Z; 33%Z; 35%Z; 37%Z; 39%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.