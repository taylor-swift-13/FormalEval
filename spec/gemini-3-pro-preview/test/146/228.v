Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (n : Z) : bool :=
    if n >? 10 then
      let f := first_digit n 100 in
      let l := n mod 10 in
      andb (Z.odd f) (Z.odd l)
    else false
  in
  fold_right (fun n acc => if is_valid n then 1 + acc else acc) 0 nums.

Example test_case: specialFilter [11; 12; 13; 14; 16] = 2.
Proof.
  compute. reflexivity.
Qed.