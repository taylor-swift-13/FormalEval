Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix helper (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
          if i * i >? n then true
          else if n mod i =? 0 then false
          else helper (i + 1) fuel'
      end
    in helper 2 (Z.to_nat n).

Fixpoint primes_less_than_aux (n : Z) (curr : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if curr >=? n then []
      else if is_prime curr then curr :: primes_less_than_aux n (curr + 1) fuel'
      else primes_less_than_aux n (curr + 1) fuel'
  end.

Definition solution (n : Z) : list Z :=
  primes_less_than_aux n 2 (Z.to_nat n).

Example test_case_1: solution 90 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89].
Proof. reflexivity. Qed.