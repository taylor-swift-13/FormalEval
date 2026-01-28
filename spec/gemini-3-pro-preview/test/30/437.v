Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example test_get_positive : get_positive_spec [0.5; -4; 2.5; 5; -8; -4; -7; -11.18889279027017; -10.5; 2.5] [0.5; 2.5; 5; 2.5].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (destruct (Rlt_dec 0 _); try lra).
  reflexivity.
Qed.