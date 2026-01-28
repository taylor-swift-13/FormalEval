Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Fixpoint is_prime_aux (n : Z) (i : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
    if i * i >? n then true
    else if (n mod i) =? 0 then false
    else is_prime_aux n (i + 1) f
  end.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else is_prime_aux n 2 (Z.to_nat n).

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [i1; i2] =>
    match i1, i2 with
    | [a1; b1], [a2; b2] =>
      let start := Z.max a1 a2 in
      let stop := Z.min b1 b2 in
      let len := stop - start in
      if is_prime len then "YES" else "NO"
    | _, _ => "NO"
    end
  | _ => "NO"
  end.

Example test_intersection: intersection [[0%Z; 3%Z]; [0%Z; 0%Z]] = "NO".
Proof. reflexivity. Qed.