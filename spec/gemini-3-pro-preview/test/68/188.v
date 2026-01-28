Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <=? 1 then false
  else if n =? 2 then true
  else if Z.even n then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 2) fuel'
      end
    in check 3 (Z.to_nat n).

Definition is_square (n : Z) : bool :=
  if n <? 0 then false
  else
    let r := Z.sqrt n in
    r * r =? n.

Definition solution (l : list Z) : list Z :=
  let count_primes := length (filter is_prime l) in
  let count_squares := length (filter is_square l) in
  [Z.of_nat count_primes; Z.of_nat count_squares].

Example test_case: solution [2; 6; 8; 2; 6] = [2; 0].
Proof. reflexivity. Qed.