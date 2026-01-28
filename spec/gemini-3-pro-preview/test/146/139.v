Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_aux (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    match n / 10 with
    | 0%nat => n
    | n' => digits_aux n' fuel'
    end
  end.

Definition first_digit (n : Z) : Z :=
  Z.of_nat (digits_aux (Z.to_nat n) (Z.to_nat n)).

Definition last_digit (n : Z) : Z :=
  n mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    if n >? 10 then
      andb (Z.odd (first_digit n)) (Z.odd (last_digit n))
    else false
  in
  fold_right (fun n acc => if predicate n then acc + 1 else acc) 0 nums.

Example test_specialFilter:
  specialFilter [-123; 456; 1111; 111] = 2.
Proof.
  vm_compute. reflexivity.
Qed.