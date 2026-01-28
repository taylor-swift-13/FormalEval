Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix iter (i : Z) (fuel : nat) :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else iter (i + 1) fuel'
      end
    in iter 2 (Z.to_nat n).

Fixpoint range (start : Z) (count : nat) : list Z :=
  match count with
  | O => []
  | S count' => start :: range (start + 1) count'
  end.

Definition solution (n : Z) : list Z :=
  filter is_prime (range 2 (Z.to_nat (n - 2))).

Example test_case: solution 26 = [2; 3; 5; 7; 11; 13; 17; 19; 23].
Proof. reflexivity. Qed.