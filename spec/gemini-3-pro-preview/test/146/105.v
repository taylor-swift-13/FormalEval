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
  get_first_digit_aux n (Z.to_nat n).

Definition get_last_digit (n : Z) : Z := n mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      (is_odd (get_first_digit n)) && (is_odd (get_last_digit n))
    else false
  in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter : specialFilter [39%Z; 241%Z; 240%Z; 39%Z] = 2%Z.
Proof. reflexivity. Qed.