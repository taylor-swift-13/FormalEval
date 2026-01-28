Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  first_digit_aux (Z.to_nat n) n.

Definition get_last_digit (n : Z) : Z := n mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (get_last_digit n))
  in Z.of_nat (length (filter check nums)).

Example test_specialFilter : specialFilter [-324%Z; 456%Z; 1111%Z; 7113%Z; 63%Z; 1111%Z] = 3%Z.
Proof. compute. reflexivity. Qed.