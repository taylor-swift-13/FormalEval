Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
      if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) (Z.to_nat (Z.abs n)).

Definition get_last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let f (x : Z) := 
    (x >? 10) && (is_odd (get_first_digit x)) && (is_odd (get_last_digit x))
  in
  Z.of_nat (length (filter f nums)).

Example test_specialFilter: specialFilter [39; 153; 99; 240; -339] = 3.
Proof. reflexivity. Qed.