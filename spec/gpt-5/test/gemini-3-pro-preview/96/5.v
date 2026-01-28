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
          else if (n mod i) =? 0 then false
          else aux (i + 1) fuel'
      end
    in aux 2 (Z.to_nat n).

Fixpoint filter_primes (limit : Z) (curr : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if curr >=? limit then []
      else if is_prime curr then curr :: filter_primes limit (curr + 1) fuel'
      else filter_primes limit (curr + 1) fuel'
  end.

Definition count_up_to (n : Z) : list Z :=
  filter_primes n 2 (Z.to_nat n).

Example test_count_up_to_0 : count_up_to 0 = [].
Proof.
  reflexivity.
Qed.