Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S p => if n <? 10 then n else first_digit_aux (n / 10) p
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux (Z.abs n) 100.

Definition last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition check (n : Z) : bool :=
  (n >? 10) && (Z.odd (first_digit n)) && (Z.odd (last_digit n)).

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter check nums)).

Example specialFilter_example : specialFilter [14%Z; -8%Z; 62%Z; 5%Z; 6%Z; -76%Z; 6%Z; 14%Z] = 0%Z.
Proof. reflexivity. Qed.