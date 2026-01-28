Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition is_odd (n : Z) : bool :=
  Z.odd n.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) :=
    if n >? 10 then
      let fd := first_digit n 100 in
      let ld := n mod 10 in
      andb (is_odd fd) (is_odd ld)
    else false
  in
  fold_right (fun x acc => if check x then acc + 1 else acc) 0 nums.

Example example_1 : specialFilter [123; 21517; 789; 111; 789] = 4.
Proof. reflexivity. Qed.