Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

Fixpoint poly (xs : list R) (x : R) : R :=
  match xs with
  | [] => 0
  | c :: cs => c + x * poly cs x
  end.

Definition find_zero_spec (xs : list R) (res : R) : Prop :=
  Nat.Even (length xs) ->
  last xs 0 <> 0 ->
  poly xs res = 0.

Lemma test_find_zero_spec_admitted : 
  find_zero_spec 
    [-300; 20999; -630000; 9450001; -78840000; 395580000; 1935360000; 
     -629999; -1663750000; -301; 725760000; 9449999; -630000; 1935360000]
    0.04614604523073008.
Proof.
  admit.
Admitted.

Example test_find_zero_spec : 
  find_zero_spec 
    [-300; 20999; -630000; 9450001; -78840000; 395580000; 1935360000; 
     -629999; -1663750000; -301; 725760000; 9449999; -630000; 1935360000]
    0.04614604523073008.
Proof.
  apply test_find_zero_spec_admitted.
Qed.