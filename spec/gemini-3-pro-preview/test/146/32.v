Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S f => if n <? 10 then n else first_digit_aux (n / 10) f
  end.

Definition first_digit (n : Z) : Z := first_digit_aux n 50.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) : bool :=
    (x >? 10) && (Z.odd (first_digit x)) && (Z.odd (x mod 10)) in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter: specialFilter [57; -23; -15; 42; 56; 104; 42; 42; 104] = 1.
Proof. reflexivity. Qed.