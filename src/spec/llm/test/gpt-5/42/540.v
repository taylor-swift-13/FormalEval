Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [2.443642398169077%R; 5.870022616692514%R; (-40)%R; 0.5090263789060623%R; 0%R; 5.9%R; 8.6%R; 3.8%R]
    [3.443642398169077%R; 6.870022616692514%R; (-39)%R; 1.5090263789060623%R; 1%R; 6.9%R; 9.6%R; 4.8%R].
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
  apply f_equal2; [lra |].
  reflexivity.
Qed.