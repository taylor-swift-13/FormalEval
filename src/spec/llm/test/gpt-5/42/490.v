Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [-0.5%R; 3.0555994730975744%R; 0%R; 5.9%R; 8.6%R; 5.9%R; 5.9%R; 5.9%R]
                 [0.5%R; 4.0555994730975744%R; 1%R; 6.9%R; 9.6%R; 6.9%R; 6.9%R; 6.9%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace (-0.5%R + 1%R) with 0.5%R by lra.
  replace (3.0555994730975744%R + 1%R) with 4.0555994730975744%R by lra.
  replace (0%R + 1%R) with 1%R by lra.
  replace (5.9%R + 1%R) with 6.9%R by lra.
  replace (8.6%R + 1%R) with 9.6%R by lra.
  replace (5.9%R + 1%R) with 6.9%R by lra.
  replace (5.9%R + 1%R) with 6.9%R by lra.
  replace (5.9%R + 1%R) with 6.9%R by lra.
  reflexivity.
Qed.