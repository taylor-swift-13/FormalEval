Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool :=
  (n mod 2 =? 1).

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux 50 n.

Definition check_num (n : Z) : bool :=
  if n >? 10 then
    let first := get_first_digit n in
    let last := n mod 10 in
    is_odd first && is_odd last
  else
    false.

Fixpoint specialFilter (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if check_num h then 1 else 0) + specialFilter t
  end.

Example test_case: specialFilter [120%Z; 122%Z; 414%Z; 214%Z; 615%Z; 218%Z; 8518%Z; 21517%Z; 2123%Z; 918%Z] = 0%Z.
Proof.
  reflexivity.
Qed.