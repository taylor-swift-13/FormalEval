 
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.

Open Scope Z_scope.

Definition is_odd (d : Z) : bool := Z.odd d.

Fixpoint get_digits (n : Z) : list Z :=
  if n <=? 0 then []
  else (n mod 10) :: get_digits (n / 10).

Definition odd_digits (n : Z) : list Z :=
  filter (fun d => is_odd d) (get_digits n).

Definition has_odd_digit (n : Z) : bool :=
  negb (forallb (fun d => negb (is_odd d)) (get_digits n)).

Definition product (l : list Z) : Z :=
  fold_right Z.mul 1 l.

Definition digits_spec (n : Z) (result : Z) : Prop :=
  n > 0 /\
  ((has_odd_digit n = false /\ result = 0) \/
   (has_odd_digit n = true /\ result = product (odd_digits n))).
