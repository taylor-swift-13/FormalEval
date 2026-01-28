Require Import List.
Import ListNotations.
Require Import ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold : below_threshold_spec [-1; -2; -3; -4] 0 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.