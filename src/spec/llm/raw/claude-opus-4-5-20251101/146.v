
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.

Open Scope Z_scope.

Definition is_odd_digit (d : Z) : bool :=
  match d with
  | 1 | 3 | 5 | 7 | 9 => true
  | _ => false
  end.

Fixpoint first_digit (n : Z) : Z :=
  if n <? 10 then n
  else first_digit (n / 10).

Definition last_digit (n : Z) : Z :=
  n mod 10.

Definition satisfies_condition (num : Z) : bool :=
  (num >? 10) && 
  is_odd_digit (first_digit num) && 
  is_odd_digit (last_digit num).

Fixpoint count_special (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: rest => 
      if satisfies_condition n then 1 + count_special rest
      else count_special rest
  end.

Definition specialFilter_spec (nums : list Z) (result : Z) : Prop :=
  result = count_special nums.
