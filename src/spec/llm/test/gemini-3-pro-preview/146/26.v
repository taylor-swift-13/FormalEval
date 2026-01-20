Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
    if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  first_digit_aux n 20.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n))
  in
  Z.of_nat (length (filter check nums)).

Example specialFilter_test :
  specialFilter [57%Z; -15%Z; 42%Z; 99%Z; 56%Z; 104%Z; 42%Z] = 2%Z.
Proof.
  compute. reflexivity.
Qed.