Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_case :
  incr_list_spec [1.5%R; 8.6%R; 3.8%R; -2.707945416165158%R; 2.443642398169077%R; 7.9%R; -2.1%R]
                 [2.5%R; 9.6%R; 4.8%R; -1.707945416165158%R; 3.443642398169077%R; 8.9%R; -1.1%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2; [lra |].
  apply f_equal2; [lra |].
  apply f_equal2; [lra |].
  apply f_equal2; [lra |].
  apply f_equal2; [lra |].
  apply f_equal2; [lra |].
  apply f_equal2; [lra |].
  reflexivity.
Qed.