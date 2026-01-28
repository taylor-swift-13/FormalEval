Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
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
  let check (n : Z) : bool :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (n mod 10)) in
  Z.of_nat (length (filter check nums)).

Example test_case_1 : specialFilter [615; 4; 6; 5; 505; 12; 6] = 1.
Proof. reflexivity. Qed.