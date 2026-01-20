Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if Z.ltb n 10 then n else get_first_digit fuel' (n / 10)
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    if Z.gtb n 10 then
      let first := get_first_digit 100 n in
      let last := n mod 10 in
      andb (Z.odd first) (Z.odd last)
    else
      false
  in
  let fix aux (l : list Z) : Z :=
    match l with
    | [] => 0
    | h :: t => (if check h then 1 else 0) + aux t
    end
  in aux nums.

Example test_specialFilter : specialFilter [14%Z; -8%Z; 62%Z; 5%Z; 6%Z; -123%Z; 39%Z] = 1%Z.
Proof. reflexivity. Qed.