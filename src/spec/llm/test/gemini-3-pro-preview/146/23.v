Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_nat (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    if Nat.ltb n 10 then n else get_first_digit_nat (Nat.div n 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  Z.of_nat (get_first_digit_nat (Z.to_nat n) (Z.to_nat n)).

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      andb (Z.odd (get_first_digit n)) (Z.odd (n mod 10))
    else false
  in
  fold_right (fun n acc => if check n then acc + 1 else acc) 0 nums.

Example test_case:
  specialFilter [57%Z; -23%Z; -15%Z; 42%Z; 99%Z; 56%Z; 104%Z; 42%Z; 42%Z] = 2%Z.
Proof.
  reflexivity.
Qed.