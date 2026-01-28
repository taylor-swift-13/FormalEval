Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if n >? 10 then
      let f := first_digit n 50 in
      let l := n mod 10 in
      andb (Z.odd f) (Z.odd l)
    else false
  in Z.of_nat (length (filter check nums)).

Example test_specialFilter: specialFilter [15; 11; 12; 103; 14; 12; 16] = 3.
Proof. reflexivity. Qed.