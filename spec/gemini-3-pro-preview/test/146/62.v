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
    (n >? 10) && 
    (Z.odd (get_first_digit n 100)) && 
    (Z.odd (n mod 10))
  in
  fold_right (fun n acc => (if check n then 1 else 0) + acc) 0 nums.

Example test_case:
  specialFilter [71; 55; -62; 7; 99; 23; 18; 99; 18] = 4.
Proof.
  reflexivity.
Qed.