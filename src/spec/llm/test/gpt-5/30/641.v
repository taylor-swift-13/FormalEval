Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x =>
    match Rlt_dec 0 x with
    | left _ => true
    | right _ => false
    end) l.

Example get_positive_spec_test :
  get_positive_spec
    [-89.04346588476734%R; -2.651030586877352%R; 33.195768044846155%R; 32.97170491287429%R; -2.25%R]
    [33.195768044846155%R; 32.97170491287429%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 (-89.04346588476734%R)) as [H1|H1].
  - exfalso; lra.
  - simpl.
    destruct (Rlt_dec 0 (-2.651030586877352%R)) as [H2|H2].
    + exfalso; lra.
    + simpl.
      destruct (Rlt_dec 0 (33.195768044846155%R)) as [H3|H3].
      * simpl.
        destruct (Rlt_dec 0 (32.97170491287429%R)) as [H4|H4].
        -- simpl.
           destruct (Rlt_dec 0 (-2.25%R)) as [H5|H5].
           ** exfalso; lra.
           ** simpl. reflexivity.
        -- exfalso; lra.
      * exfalso; lra.
Qed.