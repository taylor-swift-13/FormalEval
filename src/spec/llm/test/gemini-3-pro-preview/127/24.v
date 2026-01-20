Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => false
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) fuel'
      end
    in check 2 (Z.to_nat n).

Definition intersection (interval_1 interval_2 : list Z) : string :=
  match interval_1, interval_2 with
  | a1 :: b1 :: nil, a2 :: b2 :: nil =>
      let start := Z.max a1 a2 in
      let stop := Z.min b1 b2 in
      let dist := stop - start in
      if dist <? 0 then "NO"
      else if is_prime dist then "YES"
      else "NO"
  | _, _ => "NO"
  end.

Example test_case: intersection [-6%Z; -2%Z] [-1%Z; 0%Z] = "NO".
Proof. reflexivity. Qed.