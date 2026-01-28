Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let n := Z.abs n in
  let fix loop (fuel : nat) (x : Z) : Z :=
    match fuel with
    | O => x
    | S fuel' => if x <? 10 then x else loop fuel' (x / 10)
    end
  in loop (Z.to_nat n) n.

Definition specialFilter (nums : list Z) : Z :=
  let is_special (n : Z) : bool :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (n mod 10))
  in
  Z.of_nat (List.length (List.filter is_special nums)).

Example test_case: specialFilter [100; 101; 102; 103; 104; 102] = 2.
Proof. reflexivity. Qed.