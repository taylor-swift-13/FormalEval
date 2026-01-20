Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_case :
  incr_list_spec [-0.5%R; 1.5%R; 3.8%R; -2.1%R; 6.4%R; 7.9%R; 6.4%R]
                 [0.5%R; 2.5%R; 4.8%R; -1.1%R; 7.4%R; 8.9%R; 7.4%R].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat (apply f_equal2; [lra|]); reflexivity.
Qed.