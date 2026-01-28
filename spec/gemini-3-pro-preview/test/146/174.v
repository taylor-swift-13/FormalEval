Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z := first_digit_aux 100 (Z.abs n).

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    andb (n >? 10) (andb (Z.odd (n mod 10)) (Z.odd (get_first_digit n)))
  in
  Z.of_nat (length (filter check nums)).

Example test_case: specialFilter [123; 505; 504; 789; 504] = 3.
Proof.
  reflexivity.
Qed.