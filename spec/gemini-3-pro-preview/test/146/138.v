Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd_digit (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => 
    if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) 100%nat.

Definition get_last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition specialFilter_predicate (n : Z) : bool :=
  (n >? 10) && (is_odd_digit (get_first_digit n)) && (is_odd_digit (get_last_digit n)).

Fixpoint specialFilter (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if specialFilter_predicate h then 1 else 0) + specialFilter t
  end.

Example test_specialFilter: specialFilter [123; 21517; 789; 111] = 3.
Proof. reflexivity. Qed.