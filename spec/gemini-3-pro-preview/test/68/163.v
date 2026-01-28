Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint digits_of_Z (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      let n' := Z.abs n in
      if n' <? 10 then [n']
      else (n' mod 10) :: digits_of_Z (n' / 10) fuel'
  end.

Definition get_digits (n : Z) : list Z :=
  digits_of_Z n 100.

Definition is_odd (n : Z) : bool := Z.odd n.

Definition count_odd_digits_in_num (n : Z) : Z :=
  Z.of_nat (length (filter is_odd (get_digits n))).

Definition total_odd_digits (l : list Z) : Z :=
  fold_right Z.add 0 (map count_odd_digits_in_num l).

Definition is_even (n : Z) : bool := Z.even n.

Fixpoint remove_duplicates (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      if existsb (Z.eqb x) xs
      then remove_duplicates xs
      else x :: remove_duplicates xs
  end.

Definition count_unique_evens (l : list Z) : Z :=
  let evens := filter is_even l in
  let unique_evens := remove_duplicates evens in
  Z.of_nat (length unique_evens).

Definition solution (l : list Z) : list Z :=
  [count_unique_evens l; total_odd_digits l].

Example test_case : solution [31; 8; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2] = [2; 7].
Proof. compute. reflexivity. Qed.