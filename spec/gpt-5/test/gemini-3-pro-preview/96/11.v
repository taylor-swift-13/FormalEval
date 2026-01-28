Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint is_prime_aux (n i : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
    if i * i >? n then true
    else if n mod i =? 0 then false
    else is_prime_aux n (i + 1) fuel'
  end.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else is_prime_aux n 2 (Z.to_nat n).

Fixpoint solution_aux (n i : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if i >=? n then []
    else if is_prime i then i :: solution_aux n (i + 1) fuel'
    else solution_aux n (i + 1) fuel'
  end.

Definition solution (n : Z) : list Z :=
  solution_aux n 2 (Z.to_nat n).

Example test_case: solution 2 = [].
Proof.
  reflexivity.
Qed.