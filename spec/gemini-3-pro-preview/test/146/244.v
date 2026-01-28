Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux n (Z.to_nat n).

Definition last_digit (n : Z) : Z :=
  n mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) := (x >? 10) && (is_odd (first_digit x)) && (is_odd (last_digit x)) in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter: specialFilter [456%Z; -123%Z; 93%Z; 455%Z; 111%Z; 456%Z; -123%Z] = 2%Z.
Proof.
  compute. reflexivity.
Qed.