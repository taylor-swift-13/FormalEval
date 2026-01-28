Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Definition get_last_digit (n : Z) : Z := Z.rem n 10.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' =>
      if n <? 10 then n
      else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) (Z.to_nat (Z.abs n)).

Definition specialFilter_predicate (n : Z) : bool :=
  (n >? 10) &&
  (is_odd (get_first_digit n)) &&
  (is_odd (get_last_digit n)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if specialFilter_predicate h then 1 else 0) + specialFilter t
  end.

Example test_specialFilter: specialFilter [63%Z; 24%Z; 84%Z; 75%Z; -56%Z; 214%Z; 13%Z] = 2%Z.
Proof. reflexivity. Qed.