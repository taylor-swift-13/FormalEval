Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool :=
  (n mod 2 =? 1).

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n (Z.to_nat (Z.abs n)).

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (is_odd (n mod 10)) && (is_odd (get_first_digit n)) in
  let fix count (l : list Z) : Z :=
    match l with
    | [] => 0
    | h :: t => (if check h then 1 else 0) + count t
    end in
  count nums.

Example test_specialFilter:
  specialFilter [24%Z; -25%Z; 9%Z; 37%Z; -71%Z; -18%Z] = 1%Z.
Proof.
  vm_compute. reflexivity.
Qed.