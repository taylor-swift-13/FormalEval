Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Fixpoint is_prime_aux (n : Z) (d : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
    if d * d >? n then true
    else if n mod d =? 0 then false
    else is_prime_aux n (d + 1) f
  end.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else is_prime_aux n 2 (Z.to_nat n).

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [a; b] :: [c; d] :: nil =>
      let start := Z.max a c in
      let stop := Z.min b d in
      let width := stop - start in
      if is_prime width then "YES" else "NO"
  | _ => "NO"
  end.

Example test_intersection: intersection [[-7; -2]; [-7; -2]] = "YES".
Proof. reflexivity. Qed.