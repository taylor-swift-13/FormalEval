Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition Rgt_bool (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgt_bool x 0) l.

Example test_get_positive : 
  get_positive_spec 
    [0.5; 2.5; 5; -2.2; -2.651030586877352; -8; 9.9; -10.5; 9.9] 
    [0.5; 2.5; 5; 9.9; 9.9].
Proof.
  unfold get_positive_spec.
  unfold filter.
  unfold Rgt_bool.
  repeat (destruct (Rgt_dec _ 0); try lra).
  reflexivity.
Qed.