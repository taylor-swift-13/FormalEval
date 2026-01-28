Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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
      andb (Z.odd first) (Z.odd last)
    else false in
  let fix count (l : list Z) : Z :=
    match l with
    | [] => 0
    | x :: xs => (if check x then 1 else 0) + count xs
    end in
  count nums.

Example test_case_1: specialFilter [101%Z; 45%Z; 8518%Z; 103%Z; 104%Z; 102%Z] = 2%Z.
Proof. reflexivity. Qed.