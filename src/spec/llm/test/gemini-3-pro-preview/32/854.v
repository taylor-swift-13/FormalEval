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

Example test_find_zero_spec : find_zero_spec 
  [IZR (-300); IZR 21000; IZR 0; IZR (-630001); IZR (-78840000); IZR 395580000; 
   IZR (-1186740000); IZR 1935360000; IZR (-1663750000); IZR (-7); IZR 725760000; 
   IZR (-630000); IZR 1935360000; IZR 725760000]
  (IZR 14533619126281329 / IZR 1000000000000000000).
Proof.
  unfold find_zero_spec.
  intros _ _.
  Admitted.