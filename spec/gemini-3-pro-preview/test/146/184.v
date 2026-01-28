Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' =>
      if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) := (x >? 10) && (Z.odd x) && (Z.odd (get_first_digit x)) in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter: specialFilter [1892; 121; 122; 214; 357; 8518; 21517; 100; 918] = 2.
Proof. reflexivity. Qed.