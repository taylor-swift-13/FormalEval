Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Fixpoint is_prime_aux (n : Z) (d : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if (d * d >? n) then true
    else if (n mod d =? 0) then false
    else is_prime_aux n (d + 1) fuel'
  end.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else is_prime_aux n 2 (Z.to_nat n).

Definition solution (l : list (list Z)) : string :=
  match l with
  | [l1; l2] =>
    match l1, l2 with
    | [a; b], [c; d] =>
      let start := Z.max a c in
      let stop := Z.min b d in
      let len := Z.max 0 (stop - start) in
      if is_prime len then "YES" else "NO"
    | _, _ => "NO"
    end
  | _ => "NO"
  end.

Example test_case: solution [[7%Z; 12%Z]; [7%Z; 12%Z]] = "YES".
Proof.
  compute.
  reflexivity.
Qed.