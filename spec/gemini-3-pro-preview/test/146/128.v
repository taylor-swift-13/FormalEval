Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if n <? 10 then n else first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  fold_right (fun x acc => 
    if (x >? 10) && (Z.odd (first_digit x 100)) && (Z.odd (x mod 10)) 
    then 1 + acc 
    else acc) 0 nums.

Example test_specialFilter:
  specialFilter [120; 122; 414; 214; 357; 8518; 21517; 2123; 918] = 1.
Proof.
  compute. reflexivity.
Qed.