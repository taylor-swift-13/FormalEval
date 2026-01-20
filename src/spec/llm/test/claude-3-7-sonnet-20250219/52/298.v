Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [2000000; 10000000; 200; 7000000; -30; 6000000; 2000000] 10000000 false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.