Require Import List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold : below_threshold_spec [-3; -2; 4] 8 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.