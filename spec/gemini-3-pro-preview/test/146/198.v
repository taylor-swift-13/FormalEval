Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd_digit (n : Z) : bool :=
  Z.odd n.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && 
    (is_odd_digit (get_first_digit (Z.abs n) 100)) && 
    (is_odd_digit ((Z.abs n) mod 10)) in
  fold_right (fun n acc => if check n then 1 + acc else acc) 0 nums.

Example test_case_new : specialFilter [120; 122; 414; 214; 415; 357; 8518; 21517; 2123; 122; 918; 2123; 21517; 918] = 1.
Proof. reflexivity. Qed.