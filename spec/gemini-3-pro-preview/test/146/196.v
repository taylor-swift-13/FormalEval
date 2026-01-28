Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux fuel' (n / 10)
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux (Z.to_nat (Z.abs n)) (Z.abs n).

Definition last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition check (n : Z) : bool :=
  (n >? 10) && (is_odd (first_digit n)) && (is_odd (last_digit n)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => if check h then 1 + specialFilter t else specialFilter t
  end.

Example test_case_2: specialFilter [120; 121; 122; 357; 8518; 21517; 100; 918] = 2.
Proof.
  native_compute.
  reflexivity.
Qed.