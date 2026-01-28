Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint even_odd_count_aux (l : list Z) (e o : Z) : list Z :=
  match l with
  | [] => [e; o]
  | x :: xs =>
    if x =? 0 then [e; o]
    else if Z.even x then even_odd_count_aux xs (e + 1) o
    else even_odd_count_aux xs e (o + 1)
  end.

Definition even_odd_count (l : list Z) : list Z :=
  even_odd_count_aux l 0 0.

Example test_case: even_odd_count [0%Z; 2%Z; 6%Z; 8%Z; 10%Z; 1%Z; 3%Z; 5%Z; 36%Z; 5%Z; 9%Z; 9%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.