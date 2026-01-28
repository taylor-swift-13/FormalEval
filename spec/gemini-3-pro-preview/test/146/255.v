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

Definition check (n : Z) : bool :=
  if n >? 10 then
    let first := get_first_digit n 100 in
    let last := n mod 10 in
    (Z.odd first) && (Z.odd last)
  else false.

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if check h then 1 else 0) + specialFilter t
  end.

Example test_specialFilter : specialFilter [6%Z; 100%Z; 102%Z; 102%Z; 103%Z; 104%Z; 6%Z] = 1%Z.
Proof. compute. reflexivity. Qed.