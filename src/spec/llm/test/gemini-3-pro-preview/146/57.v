Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else digits_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  digits_aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let is_special (n : Z) :=
    (n >? 10) && 
    (Z.odd (get_first_digit n)) && 
    (Z.odd (n mod 10))
  in
  Z.of_nat (length (filter is_special nums)).

Example example : specialFilter [57; -15; 99; 56; 104; 42] = 2.
Proof. reflexivity. Qed.