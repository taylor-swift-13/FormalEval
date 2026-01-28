Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition get_positive_spec (l : list bool) (res : list bool) : Prop :=
  res = filter (fun x => x) l.

Example test_get_positive : get_positive_spec [false; true; false; true; true; true] [true; true; true; true].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.