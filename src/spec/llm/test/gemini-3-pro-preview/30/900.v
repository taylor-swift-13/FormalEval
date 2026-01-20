Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [5.803598881698951; 25.221353337136023; 33.195768044846155; -2.25; -2.25] [5.803598881698951; 25.221353337136023; 33.195768044846155].
Proof.
  unfold get_positive_spec.
  unfold filter.
  destruct (Rgt_dec 5.803598881698951 0); [ | exfalso; lra].
  destruct (Rgt_dec 25.221353337136023 0); [ | exfalso; lra].
  destruct (Rgt_dec 33.195768044846155 0); [ | exfalso; lra].
  destruct (Rgt_dec (-2.25) 0); [ exfalso; lra | ].
  destruct (Rgt_dec (-2.25) 0); [ exfalso; lra | ].
  reflexivity.
Qed.