Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec 
  [9.9%R; 24.93175152910768%R; -3.1836537136945844%R; -3.1836537136945844%R; -0.42322814636615796%R] 
  [9.9%R; 24.93175152910768%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 9.9 0); try (exfalso; lra).
  destruct (Rgt_dec 24.93175152910768 0); try (exfalso; lra).
  destruct (Rgt_dec (-3.1836537136945844) 0); try (exfalso; lra).
  destruct (Rgt_dec (-3.1836537136945844) 0); try (exfalso; lra).
  destruct (Rgt_dec (-0.42322814636615796) 0); try (exfalso; lra).
  reflexivity.
Qed.