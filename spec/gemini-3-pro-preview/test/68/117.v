Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else if n =? 2 then true
  else if Z.even n then false
  else
    let fix aux (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if n mod i =? 0 then false
        else aux (i + 2) fuel'
      end
    in aux 3 (Z.to_nat n).

Definition solution (l : list Z) : list Z :=
  let p := length (filter is_prime l) in
  let o := length (filter Z.odd l) in
  [Z.of_nat p; Z.of_nat o].

Example test_case : solution [2; 4; 6; 8; 2] = [2; 0].
Proof. reflexivity. Qed.