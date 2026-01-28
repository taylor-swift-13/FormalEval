Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  first_digit_aux (Z.to_nat n) n.

Definition get_last_digit (n : Z) : Z :=
  n mod 10.

Definition check_num (n : Z) : bool :=
  (n >? 10) && (is_odd (get_first_digit n)) && (is_odd (get_last_digit n)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => if check_num h then 1 + specialFilter t else specialFilter t
  end.

Example test_case_2: specialFilter [43; -12; 93; 125; 121; 109] = 4.
Proof. reflexivity. Qed.