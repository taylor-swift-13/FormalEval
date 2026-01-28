Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if n <? 10 then n else first_digit (n / 10) fuel'
  end.

Definition check_element (n : Z) : bool :=
  if n >? 10 then
    let first := first_digit n 100 in
    let last := n mod 10 in
    (Z.odd first) && (Z.odd last)
  else
    false.

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if check_element h then 1 else 0) + specialFilter t
  end.

Example test_specialFilter: specialFilter [63%Z; -55%Z; 84%Z; 83%Z; 75%Z; 13%Z; 12%Z; -55%Z; 63%Z] = 2%Z.
Proof. simpl. reflexivity. Qed.