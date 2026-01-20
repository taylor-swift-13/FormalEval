Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [0.5%R; (-4)%R; 2.5%R; 5%R; (-8)%R; (-4)%R; (-7)%R; (-11.18889279027017)%R; (-10.5)%R; 2.5%R]
                    [0.5%R; 2.5%R; 5%R; 2.5%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 0.5 0); [ | exfalso; lra].
  simpl.
  destruct (Rgt_dec (-4) 0); [ exfalso; lra | ].
  simpl.
  destruct (Rgt_dec 2.5 0); [ | exfalso; lra].
  simpl.
  destruct (Rgt_dec 5 0); [ | exfalso; lra].
  simpl.
  destruct (Rgt_dec (-8) 0); [ exfalso; lra | ].
  simpl.
  destruct (Rgt_dec (-4) 0); [ exfalso; lra | ].
  simpl.
  destruct (Rgt_dec (-7) 0); [ exfalso; lra | ].
  simpl.
  destruct (Rgt_dec (-11.18889279027017) 0); [ exfalso; lra | ].
  simpl.
  destruct (Rgt_dec (-10.5) 0); [ exfalso; lra | ].
  simpl.
  destruct (Rgt_dec 2.5 0); [ | exfalso; lra].
  simpl.
  reflexivity.
Qed.