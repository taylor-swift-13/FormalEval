Require Import ZArith.
Require Import List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope Z_scope.

Definition sign (x : Z) : Z :=
  if x <? 0 then -1
  else if x >? 0 then 1
  else 0.

Definition abs (x : Z) : Z :=
  if x <? 0 then -x else x.

Fixpoint sum_magnitudes (arr : list Z) : Z :=
  match arr with
  | nil => 0
  | x :: xs => abs x + sum_magnitudes xs
  end.

Fixpoint product_signs (arr : list Z) : Z :=
  match arr with
  | nil => 1
  | x :: xs => sign x * product_signs xs
  end.

Fixpoint contains_zero (arr : list Z) : bool :=
  match arr with
  | nil => false
  | x :: xs => if x =? 0 then true else contains_zero xs
  end.

Definition prod_signs_spec (arr : list Z) (result : option Z) : Prop :=
  match arr with
  | nil => result = None
  | _ => 
    if contains_zero arr then result = Some 0
    else result = Some (sum_magnitudes arr * product_signs arr)
  end.

Example test_prod_signs : prod_signs_spec [0; 1; 2; 2; 3; -4; -5; 10; 7; 8; -9; -10; -5; -10; 7; 1] (Some 0).
Proof.
  (* Unfold the specification definition *)
  unfold prod_signs_spec.
  
  (* Simplify the expression. 
     This evaluates contains_zero, sum_magnitudes, and product_signs
     for the concrete list. *)
  simpl.
  
  (* The simplification results in Some 0 = Some 0, which is trivially true *)
  reflexivity.
Qed.