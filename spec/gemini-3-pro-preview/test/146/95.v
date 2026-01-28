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

Definition first_digit (n : Z) : Z :=
  first_digit_aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) : bool :=
    (x >? 10) && (Z.odd (first_digit x)) && (Z.odd (x mod 10)) in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter: specialFilter [57; -15; 56; 104; 42] = 1.
Proof. reflexivity. Qed.