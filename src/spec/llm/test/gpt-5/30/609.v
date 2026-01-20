Require Import Coq.Lists.List.
Import ListNotations.

Definition get_positive_spec (l : list bool) (res : list bool) : Prop :=
  res = filter (fun x => x) l.

Example get_positive_spec_test :
  get_positive_spec [false; true; false; true; true; true] [true; true; true; true].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.