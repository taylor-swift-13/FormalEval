Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zcompare.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [2000000; 10000001; 9000000; 8000000; 6000000; 2000000; 8000000] 10000001 false.
Proof.
  unfold below_threshold_spec.
  simpl.
  (* compute the forallb (fun x => Z.ltb x 10000001) on the list *)
  (* Z.ltb returns true for elements strictly less than 10000001 *)
  (* Here 10000001 is exactly equal to one element in the list, so that comparison returns false *)
  reflexivity.
Qed.