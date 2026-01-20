
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope Z_scope.

Fixpoint count_digit_7 (n : Z) : Z :=
  if n <=? 0 then 0
  else (if (n mod 10 =? 7) then 1 else 0) + count_digit_7 (n / 10).

Fixpoint fizz_buzz_helper (i : Z) (n : Z) (acc : Z) : Z :=
  if i >=? n then acc
  else
    let new_acc :=
      if ((i mod 11 =? 0) || (i mod 13 =? 0))%bool
      then acc + count_digit_7 i
      else acc
    in fizz_buzz_helper (i + 1) n new_acc.

Definition fizz_buzz_spec (n : Z) (result : Z) : Prop :=
  result = fizz_buzz_helper 0 n 0.
