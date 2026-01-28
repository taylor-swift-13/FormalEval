Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
        else if (n mod i) =? 0 then false
        else check (i + 1) fuel'
      end
    in check 2 (Z.to_nat n).

Fixpoint primes_less_than_aux (n : Z) (curr : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if curr >=? n then []
      else if is_prime curr then curr :: primes_less_than_aux n (curr + 1) fuel'
      else primes_less_than_aux n (curr + 1) fuel'
  end.

Definition primes_less_than (n : Z) : list Z :=
  primes_less_than_aux n 2 (Z.to_nat n).

Example test_primes_less_than: primes_less_than 15 = [2; 3; 5; 7; 11; 13].
Proof. reflexivity. Qed.