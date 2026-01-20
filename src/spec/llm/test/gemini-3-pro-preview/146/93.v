Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      let f := first_digit n 100 in
      let l := n mod 10 in
      andb (Z.odd f) (Z.odd l)
    else false
  in
  fold_right (fun x acc => if check x then acc + 1 else acc) 0 nums.

Example test_specialFilter: specialFilter [76%Z; 6%Z; 89%Z; -12%Z; 77%Z; 13%Z; 196%Z; 196%Z] = 2%Z.
Proof. reflexivity. Qed.