Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [21.28666897792971%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R; -3.1836537136945844%R; -1.5%R] [21.28666897792971%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (destruct (Rgt_dec _ 0); try (exfalso; lra)).
  reflexivity.
Qed.