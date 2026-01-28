Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) :=
    if x >? 10 then
      let f := get_first_digit x in
      let l := x mod 10 in
      andb (Z.odd f) (Z.odd l)
    else false
  in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [-2; 1111; 4; 6; 8; 10; 12; 15] = 2.
Proof. reflexivity. Qed.