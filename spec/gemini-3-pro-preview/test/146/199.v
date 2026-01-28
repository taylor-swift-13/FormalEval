Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n (Z.to_nat n).

Definition get_last_digit (n : Z) : Z :=
  n mod 10.

Definition is_odd_digit (n : Z) : bool :=
  Z.odd n.

Definition check_num (n : Z) : bool :=
  if n >? 10 then
    (is_odd_digit (get_first_digit n)) && (is_odd_digit (get_last_digit n))
  else
    false.

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter check_num nums)).

Example test_specialFilter:
  specialFilter [120; 122; 214; 218; 8518; 21517; 2123; 918; 2123] = 0.
Proof.
  reflexivity.
Qed.