Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint all_digits_even_aux (n : Z) (fuel : nat) : bool :=
  match fuel with
  | 0%nat => true
  | S fuel' =>
    if Z.ltb n 10 then Z.even n
    else if Z.even (Z.modulo n 10) then all_digits_even_aux (Z.div n 10) fuel' else false
  end.

Definition all_digits_even (z : Z) : bool :=
  let n := Z.abs z in
  all_digits_even_aux n 20.

Definition solution (l : list Z) : list Z :=
  let l' := filter (fun x => Z.ltb (Z.abs x) 100) l in
  let count_even := length (filter all_digits_even l') in
  let count_odd := length (filter (fun x => negb (all_digits_even x)) l') in
  [Z.of_nat count_even; Z.of_nat count_odd].

Example test_case:
  solution [7; 9; 1; 5; 10000; 3; 11; 13; 17; 19; 21; 23; 25; 27; 29; 9; 10; 31; 33; 35; 37; 39; 4; 2; 9; 5] = [2; 23].
Proof. reflexivity. Qed.