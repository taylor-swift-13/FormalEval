Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else if n =? 2 then true
  else if Z.even n then false
  else
    let fix aux (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else aux (i + 2) fuel'
      end
    in aux 3 (Z.to_nat n).

Definition solution (l : list Z) : list Z :=
  let primes := filter is_prime l in
  let non_primes := filter (fun x => negb (is_prime x)) l in
  [Z.of_nat (length primes); Z.of_nat (length non_primes)].

Example test_case: solution [1; 2; 3] = [2; 1].
Proof.
  reflexivity.
Qed.