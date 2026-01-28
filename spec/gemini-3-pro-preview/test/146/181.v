Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S p => if n <? 10 then n else get_first_digit_aux p (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  let n' := Z.abs n in
  get_first_digit_aux (Z.to_nat (Z.log2 n' + 1)) n'.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd n)
  in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [100; 120; 121; 122; 214; 357; 8518; 21517; 100; 918] = 2.
Proof.
  reflexivity.
Qed.