Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition check (n : Z) : bool :=
  if n >? 10 then
    let fd := get_first_digit n 100 in
    let ld := n mod 10 in
    andb (is_odd fd) (is_odd ld)
  else false.

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter check nums)).

Example test_specialFilter: specialFilter [240; 39; 152; 241; -339] = 1.
Proof. reflexivity. Qed.