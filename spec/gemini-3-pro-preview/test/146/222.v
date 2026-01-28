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

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n in
      let last := n mod 10 in
      andb (Z.odd first) (Z.odd last)
    else false
  in Z.of_nat (length (filter check nums)).

Example test_specialFilter: specialFilter [104; 456; -123; 93; 456; 111; 456] = 2.
Proof. reflexivity. Qed.