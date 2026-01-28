Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let p (n : Z) :=
    if n >? 10 then
      let first := get_first_digit n (Z.to_nat n) in
      let last := n mod 10 in
      (Z.odd first) && (Z.odd last)
    else false
  in Z.of_nat (length (filter p nums)).

Example test_specialFilter: specialFilter [-23; -15; 42; 56; -339; 42; 104] = 0.
Proof.
  reflexivity.
Qed.