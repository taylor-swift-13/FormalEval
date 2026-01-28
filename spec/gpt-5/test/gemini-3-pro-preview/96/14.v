Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix aux (i : Z) (fuel : nat) :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i =? 0) then false
        else aux (i + 1) fuel'
      end
    in aux 2 (Z.to_nat n).

Fixpoint range (start : Z) (len : nat) : list Z :=
  match len with
  | O => []
  | S len' => start :: range (start + 1) len'
  end.

Definition all_primes (n : Z) : list Z :=
  filter is_prime (range 2 (Z.to_nat (n - 2))).

Example test_all_primes : all_primes 17 = [2; 3; 5; 7; 11; 13].
Proof. reflexivity. Qed.