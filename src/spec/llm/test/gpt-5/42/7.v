Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_case :
  incr_list_spec [2.5%R; 3.7%R; 8.9%R; 1.2%R; 0.5%R]
                 [3.5%R; 4.7%R; 9.9%R; 2.2%R; 1.5%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace 3.5%R with (2.5%R + 1%R) by lra.
  replace 4.7%R with (3.7%R + 1%R) by lra.
  replace 9.9%R with (8.9%R + 1%R) by lra.
  replace 2.2%R with (1.2%R + 1%R) by lra.
  replace 1.5%R with (0.5%R + 1%R) by lra.
  reflexivity.
Qed.