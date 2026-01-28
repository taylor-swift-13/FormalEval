Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Fixpoint prime_check (n : Z) (i : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' => 
    if i * i >? n then true
    else if (n mod i) =? 0 then false
    else prime_check n (i + 1) fuel'
  end.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else prime_check n 2 (Z.to_nat n).

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [a; b] :: [c; d] :: nil =>
      let start := Z.max a c in
      let stop := Z.min b d in
      let len := stop - start in
      if is_prime len then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case: intersection [[-10; 1]; [-2; 2]] = "YES".
Proof.
  compute.
  reflexivity.
Qed.