Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.to_nat n) n.

Definition specialFilter_predicate (n : Z) : bool :=
  (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if specialFilter_predicate h then 1 else 0) + specialFilter t
  end.

Example test_specialFilter: specialFilter [102; 505; 789; 102] = 2.
Proof.
  reflexivity.
Qed.