Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

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
          else if n mod i =? 0 then false
          else aux (i + 2) fuel'
      end
    in aux 3 (Z.to_nat n).

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [i1; i2] =>
      match i1, i2 with
      | [a; b], [c; d] =>
          let start := Z.max a c in
          let stop := Z.min b d in
          let len := stop - start in
          if is_prime len then "YES" else "NO"
      | _, _ => "NO"
      end
  | _ => "NO"
  end.

Example test_intersection: intersection [[-11%Z; 2%Z]; [-1%Z; -1%Z]] = "NO".
Proof. reflexivity. Qed.