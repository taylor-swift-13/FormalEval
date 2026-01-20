Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else if n =? 2 then true
  else if Z.even n then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => false
      | S fuel' =>
          if i * i >? n then true
          else if (n mod i) =? 0 then false
          else check (i + 2) fuel'
      end
    in check 3 (Z.to_nat n).

Definition intersection (l1 l2 : list Z) : string :=
  match l1, l2 with
  | [a; b], [c; d] =>
      let start := Z.max a c in
      let stop := Z.min b d in
      let len := stop - start in
      if is_prime len then "YES" else "NO"
  | _, _ => "NO"
  end.

Example test_intersection : intersection [1; 2] [3; 5] = "NO".
Proof.
  reflexivity.
Qed.