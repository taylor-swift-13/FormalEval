Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_aux (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if n <? 10 then [n]
    else (n mod 10) :: digits_aux (n / 10) fuel'
  end.

Definition digits (n : Z) : list Z :=
  digits_aux n 100%nat.

Definition sum_digits_signed (n : Z) : Z :=
  let l := digits (Z.abs n) in
  let l_rev := rev l in
  match l_rev with
  | [] => 0
  | x :: xs =>
    let first := if n <? 0 then -x else x in
    fold_left Z.add xs first
  end.

Definition count_nums (l : list Z) : Z :=
  fold_left (fun acc x => if sum_digits_signed x >? 0 then acc + 1 else acc) l 0.

Example test_case_2: count_nums [22; -33; -46; 89; -91; 128] = 4.
Proof. reflexivity. Qed.