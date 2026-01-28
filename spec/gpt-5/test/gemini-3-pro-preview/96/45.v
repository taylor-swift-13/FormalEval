Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix aux (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if n mod i =? 0 then false
        else aux (i + 1) fuel'
      end
    in aux 2 (Z.to_nat n).

Fixpoint range_aux (n : nat) (acc : list Z) : list Z :=
  match n with
  | O => acc
  | S n' => range_aux n' (Z.of_nat n' :: acc)
  end.

Definition range (n : nat) : list Z := range_aux n [].

Definition primes_less_than (n : Z) : list Z :=
  filter is_prime (range (Z.to_nat n)).

Example test_primes_less_than: primes_less_than 14 = [2; 3; 5; 7; 11; 13].
Proof. reflexivity. Qed.