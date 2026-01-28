Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else if n =? 2 then true
  else if Z.even n then false
  else
    let fix aux (i : Z) (fuel : nat) :=
      match fuel with
      | O => false
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else aux (i + 2) fuel'
      end
    in aux 3 (Z.to_nat n).

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [a; b] :: [c; d] :: nil =>
      let start := Z.max a c in
      let end_ := Z.min b d in
      let len := end_ - start in
      if is_prime len then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case_1: intersection [[-2%Z; 2%Z]; [-4%Z; 0%Z]] = "YES".
Proof. reflexivity. Qed.