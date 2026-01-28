Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.

Definition triples_sum_to_zero (l : list Z) : bool :=
  let fix exists_sum2 (target : Z) (l : list Z) : bool :=
    match l with
    | [] => false
    | y :: ys => 
        let fix exists_val (t : Z) (xs : list Z) : bool :=
          match xs with
          | [] => false
          | z :: zs => (z =? t) || exists_val t zs
          end
        in exists_val (target - y) ys || exists_sum2 target ys
    end
  in
  let fix aux (l : list Z) : bool :=
    match l with
    | [] => false
    | x :: xs => exists_sum2 (0 - x) xs || aux xs
    end
  in aux l.

Example test_triples_sum_to_zero : triples_sum_to_zero [120; 122; 414; 214; 8518; 21517; 2123; 918] = false.
Proof. reflexivity. Qed.