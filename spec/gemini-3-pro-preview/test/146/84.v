Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S p => if n <? 10 then n else get_first_digit (n / 10) p
  end.

Definition check (n : Z) : bool :=
  if n >? 10 then
    andb (is_odd (n mod 10)) (is_odd (get_first_digit n (Z.to_nat n)))
  else false.

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => if check h then 1 + specialFilter t else specialFilter t
  end.

Example test_case: specialFilter [101; -35; 44; -67; -67] = 1.
Proof. reflexivity. Qed.