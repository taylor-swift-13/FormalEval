Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : nat) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Nat.ltb n 10 then Z.of_nat n
      else first_digit_aux (Nat.div n 10) fuel'
  end.

Definition get_first_digit (z : Z) : Z :=
  let n := Z.to_nat (Z.abs z) in
  first_digit_aux n n.

Definition get_last_digit (z : Z) : Z :=
  Z.modulo (Z.abs z) 10.

Definition specialFilter (nums : list Z) : Z :=
  let p (x : Z) :=
    (x >? 10) &&
    (Z.odd (get_first_digit x)) &&
    (Z.odd (get_last_digit x))
  in
  Z.of_nat (length (filter p nums)).

Example test_specialFilter_new : specialFilter [120; 122; 414; 214; 357; 8518; 21517; 2123; 918; 2123; 21517] = 1%Z.
Proof.
  compute. reflexivity.
Qed.