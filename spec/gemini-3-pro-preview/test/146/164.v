Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  first_digit_aux 100 n.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    if n >? 10 then
      let f := get_first_digit n in
      let l := n mod 10 in
      andb (Z.odd f) (Z.odd l)
    else false
  in Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [63; 24; 84; 75; -56; 214; 13; -56] = 2.
Proof. reflexivity. Qed.