Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S p => if n <? 10 then n else get_first_digit_aux (n / 10) p
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n (Z.to_nat n).

Definition get_last_digit (n : Z) : Z :=
  n mod 10.

Definition check (n : Z) : bool :=
  (n >? 10) && (is_odd (get_first_digit n)) && (is_odd (get_last_digit n)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if check h then 1 else 0) + specialFilter t
  end.

Example test_case_2: specialFilter [121; 120; 121; 122; 214; 357; 8518; 21517; 2123; 918; 358; 357] = 4.
Proof.
  vm_compute.
  reflexivity.
Qed.