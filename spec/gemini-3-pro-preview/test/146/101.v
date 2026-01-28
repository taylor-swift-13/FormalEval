Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit fuel' (n / 10)
  end.

Definition first_digit (n : Z) : Z :=
  get_first_digit 100 n.

Definition last_digit (n : Z) : Z :=
  n mod 10.

Definition specialFilter_predicate (n : Z) : bool :=
  (n >? 10) && (Z.odd (first_digit n)) && (Z.odd (last_digit n)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if specialFilter_predicate h then 1 else 0) + specialFilter t
  end.

Example test_case: specialFilter [14; -8; -18; 6; -76; 6; 6] = 0.
Proof. reflexivity. Qed.