Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) 100%nat.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n))
  in
  let fix count (l : list Z) : Z :=
    match l with
    | [] => 0
    | h :: t => (if check h then 1 else 0) + count t
    end
  in count nums.

Example test_specialFilter: specialFilter [12; 239; 152; 39; 240; -339] = 1.
Proof. reflexivity. Qed.