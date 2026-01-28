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
      | S f => 
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) f
      end
    in check 2 (Z.to_nat n).

Fixpoint range (start : Z) (count : nat) : list Z :=
  match count with
  | O => []
  | S c => start :: range (start + 1) c
  end.

Definition all_primes (n : Z) : list Z :=
  filter is_prime (range 2 (Z.to_nat (n - 2))).

Example test_all_primes : all_primes 92 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89].
Proof. reflexivity. Qed.