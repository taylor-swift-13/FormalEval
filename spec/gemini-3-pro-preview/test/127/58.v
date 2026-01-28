Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Fixpoint is_prime_check (n : Z) (i : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      if i * i >? n then true
      else if n mod i =? 0 then false
      else is_prime_check n (i + 1) fuel'
  end.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else is_prime_check n 2 (Z.to_nat n).

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

Example test_case: intersection [[6%Z; 10%Z]; [6%Z; 10%Z]] = "NO".
Proof.
  compute.
  reflexivity.
Qed.