Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  first_digit_aux (Z.abs n) 50.

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) : bool :=
    (x >? 10) && (Z.odd (x mod 10)) && (Z.odd (get_first_digit x)) in
  fold_right (fun x acc => if check x then acc + 1 else acc) 0 nums.

Example test_specialFilter:
  specialFilter [455; 123; 789; 111; 21518; 789] = 4.
Proof. reflexivity. Qed.