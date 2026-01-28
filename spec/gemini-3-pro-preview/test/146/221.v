Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux 100 (Z.abs n).

Definition specialFilter_predicate (n : Z) : bool :=
  (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (n mod 10)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if specialFilter_predicate h then 1 else 0) + specialFilter t
  end.

Example test_specialFilter : specialFilter [-123; 456; 789; 111; 111] = 3.
Proof.
  compute.
  reflexivity.
Qed.