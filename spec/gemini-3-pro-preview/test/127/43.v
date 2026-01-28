Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix aux (i : Z) (fuel : nat) :=
      match fuel with
      | O => true
      | S fuel' =>
          if i * i >? n then true
          else if n mod i =? 0 then false
          else aux (i + 1) fuel'
      end
    in aux 2 (Z.to_nat n).

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [x1 :: y1 :: nil; x2 :: y2 :: nil] =>
      let start := Z.max x1 x2 in
      let stop := Z.min y1 y2 in
      let len := stop - start in
      if is_prime len then "YES" else "NO"
  | _ => "NO"
  end.

Example test_intersection:
  intersection [[-15%Z; 12%Z]; [-10%Z; 10%Z]] = "NO".
Proof.
  reflexivity.
Qed.