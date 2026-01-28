Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
      if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux 100%nat n.

Definition get_last_digit (n : Z) : Z :=
  n mod 10.

Definition check (n : Z) : bool :=
  if n >? 10 then
    let f := get_first_digit n in
    let l := get_last_digit n in
    (is_odd f) && (is_odd l)
  else
    false.

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => 
      if check h then 1 + specialFilter t else specialFilter t
  end.

Example test_case_1 : specialFilter [-23; -15; 42; 99; 154; 42; -15] = 1.
Proof. reflexivity. Qed.