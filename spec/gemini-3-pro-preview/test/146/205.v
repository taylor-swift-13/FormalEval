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
  get_first_digit_aux (Z.abs n) 100.

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) : bool :=
    (x >? 10) && (Z.odd (x mod 10)) && (Z.odd (get_first_digit x))
  in Z.of_nat (length (filter check nums)).

Example test_specialFilter: specialFilter [100; 101; 103; 83; 102] = 2.
Proof.
  compute. reflexivity.
Qed.