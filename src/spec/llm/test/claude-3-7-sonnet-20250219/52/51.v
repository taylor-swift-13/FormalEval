Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import ZArith.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => (x <? t)%Z) l.

Example test_below_threshold :
  below_threshold_spec [7; -2; -3; -3; -4] 0 false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.