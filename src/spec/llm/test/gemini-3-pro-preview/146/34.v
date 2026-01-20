Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if Z.ltb n 10 then n else get_first_digit (Z.div n 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let valid (n : Z) :=
    (Z.gtb n 10) &&
    (Z.odd (n mod 10)) &&
    (Z.odd (get_first_digit n 100))
  in
  fold_right (fun n acc => if valid n then acc + 1 else acc) 0 nums.

Example test_case : specialFilter [6%Z; 12%Z; 22%Z; 12%Z] = 0%Z.
Proof. reflexivity. Qed.