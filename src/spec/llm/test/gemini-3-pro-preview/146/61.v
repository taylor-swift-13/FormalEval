Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S f => if n <? 10 then n else get_first_digit (n / 10) f
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n 100 in
      let last := n mod 10 in
      (Z.odd first) && (Z.odd last)
    else false
  in
  fold_right (fun x acc => (if check x then 1 else 0) + acc) 0 nums.

Example test_specialFilter:
  specialFilter [57; -23; -15; 42; 104; 42; 42; 104; 42] = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.