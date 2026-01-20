Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_fuel fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_fuel (Z.to_nat n) n.

Definition specialFilter_predicate (n : Z) : bool :=
  if n >? 10 then
    andb (Z.odd (get_first_digit n)) (Z.odd (n mod 10))
  else false.

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if specialFilter_predicate h then 1 else 0) + specialFilter t
  end.

Example test_specialFilter: specialFilter [10; 12; 22; -76; 37] = 1.
Proof. reflexivity. Qed.