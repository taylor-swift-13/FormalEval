Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [1.2%R; 2.5%R; 3.7%R] [1.2%R; 2.5%R; 3.7%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 1.2%R 0%R) as [H1|H1]; [| exfalso; lra].
  simpl.
  destruct (Rgt_dec 2.5%R 0%R) as [H2|H2]; [| exfalso; lra].
  simpl.
  destruct (Rgt_dec 3.7%R 0%R) as [H3|H3]; [| exfalso; lra].
  simpl.
  reflexivity.
Qed.