Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import ZArith.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [10000000; 9000000; 8000000; 2000; 6000000; 100; 8000000] 10000001 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.