Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n (Z.to_nat n).

Definition specialFilter (nums : list Z) : Z :=
  let p (n : Z) :=
    if n >? 10 then
      andb (Z.odd (get_first_digit n)) (Z.odd (n mod 10))
    else false
  in
  Z.of_nat (length (filter p nums)).

Example test_case: specialFilter [615; 4; 5; 14; 12; 6] = 0.
Proof. reflexivity. Qed.