Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition specialFilter (nums : list Z) : Z :=
  let first_digit (n : Z) : Z :=
    let fix aux (n : Z) (fuel : nat) : Z :=
      match fuel with
      | O => n
      | S fuel' => if n <? 10 then n else aux (n / 10) fuel'
      end
    in aux (Z.abs n) 100%nat
  in
  let keep (n : Z) : bool :=
    (n >? 10) &&
    (Z.odd (n mod 10)) &&
    (Z.odd (first_digit n))
  in
  Z.of_nat (length (filter keep nums)).

Example test_specialFilter: specialFilter [-122; 101; 102; 103] = 2.
Proof.
  reflexivity.
Qed.