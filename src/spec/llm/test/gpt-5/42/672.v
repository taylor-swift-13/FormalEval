Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_example :
  incr_list_spec [3.8%R; -2.1%R; 6.4%R; 8.002455154762643%R]
                 [4.8%R; -1.1%R; 7.4%R; 9.002455154762643%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  reflexivity.
Qed.