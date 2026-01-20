Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n 100.

Definition specialFilter_check (n : Z) : bool :=
  (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if specialFilter_check h then 1 else 0) + specialFilter t
  end.

Example test_case: specialFilter [24%Z; -25%Z; 9%Z; 37%Z; -71%Z; -17%Z] = 1%Z.
Proof. reflexivity. Qed.