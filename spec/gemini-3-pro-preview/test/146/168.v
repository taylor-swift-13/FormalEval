Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S f => if n <? 10 then n else get_first_digit (n / 10) f
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) : bool :=
    if x >? 10 then
      let first := get_first_digit x 100 in
      let last := x mod 10 in
      (first mod 2 =? 1) && (last mod 2 =? 1)
    else false
  in Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [-2%Z; 4%Z; 6%Z; 8%Z; 14%Z; 10%Z; 1892%Z; 103%Z; 15%Z; 10%Z] = 2%Z.
Proof.
  vm_compute. reflexivity.
Qed.