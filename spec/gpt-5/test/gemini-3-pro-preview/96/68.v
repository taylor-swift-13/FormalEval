Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if n mod i =? 0 then false
        else check (i + 1) fuel'
      end
    in check 2 (Z.to_nat n).

Fixpoint all_primes_iter (n : Z) (curr : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if curr >=? n then []
    else
      if is_prime curr then curr :: all_primes_iter n (curr + 1) fuel'
      else all_primes_iter n (curr + 1) fuel'
  end.

Definition all_primes (n : Z) : list Z :=
  all_primes_iter n 2 (Z.to_nat n).

Example test_case: all_primes 84 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83].
Proof.
  vm_compute. reflexivity.
Qed.