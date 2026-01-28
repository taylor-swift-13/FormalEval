Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [9.9; 33.195768044846155; 10.538283343362641; -2.25] [9.9; 33.195768044846155; 10.538283343362641].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 9.9 0); [ | exfalso; lra ].
  destruct (Rgt_dec 33.195768044846155 0); [ | exfalso; lra ].
  destruct (Rgt_dec 10.538283343362641 0); [ | exfalso; lra ].
  destruct (Rgt_dec (-2.25) 0).
  - exfalso; lra.
  - reflexivity.
Qed.