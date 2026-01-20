Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_nat (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0%nat => n
  | S fuel' => if Nat.ltb n 10 then n else get_first_digit_nat (Nat.div n 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  let n_nat := Z.to_nat (Z.abs n) in
  Z.of_nat (get_first_digit_nat n_nat n_nat).

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    andb (n >? 10) (andb (Z.odd (get_first_digit n)) (Z.odd n))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [11%Z; 232%Z; 324%Z; -876%Z; 799%Z] = 2%Z.
Proof.
  compute. reflexivity.
Qed.