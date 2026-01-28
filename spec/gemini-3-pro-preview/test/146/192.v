Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition is_odd (n : Z) : bool := (n mod 2 =? 1).

Definition last_digit (n : Z) : Z := (Z.abs n) mod 10.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => 
    let abs_n := Z.abs n in
    if abs_n <? 10 then abs_n
    else first_digit_aux (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z := first_digit_aux n 20.

Definition check (n : Z) : bool :=
  andb (n >? 10) 
       (andb (is_odd (first_digit n)) 
             (is_odd (last_digit n))).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => if check h then 1 + specialFilter t else specialFilter t
  end.

Example test_specialFilter_2 : 
  specialFilter [100; 8518; 102; 103; 104; 102] = 1.
Proof.
  reflexivity.
Qed.