Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) :=
    if n >? 10 then
      let first := get_first_digit n in
      let last := n mod 10 in
      (Z.odd first) && (Z.odd last)
    else false
  in
  let fix count (l : list Z) : Z :=
    match l with
    | [] => 0
    | h :: t => (if check h then 1 else 0) + count t
    end
  in count nums.

Example test_specialFilter: specialFilter [-62; 232; 324; -877; -876; 152; 799; 324] = 1.
Proof. reflexivity. Qed.