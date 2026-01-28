Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit fuel' (n / 10)
  end.

Definition first_digit (n : Z) : Z :=
  get_first_digit (Z.to_nat n) n.

Definition last_digit (n : Z) : Z :=
  n mod 10.

Definition check (n : Z) : bool :=
  if n >? 10 then
    andb (is_odd (first_digit n)) (is_odd (last_digit n))
  else
    false.

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => if check h then 1 + specialFilter t else specialFilter t
  end.

Example test_specialFilter: specialFilter [-23; 42; 99; 56; 104; 42] = 1.
Proof. reflexivity. Qed.