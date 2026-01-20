Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_case :
  incr_list_spec
    [-0.5%R; 3.0555994730975744%R; 0%R; 5.9%R; 8.6%R; 5.9%R; 7.041313375938212%R; 5.9%R; 1.5%R; 5.9%R; 8.6%R]
    (List.map (fun x => x + 1%R)
      [-0.5%R; 3.0555994730975744%R; 0%R; 5.9%R; 8.6%R; 5.9%R; 7.041313375938212%R; 5.9%R; 1.5%R; 5.9%R; 8.6%R]).
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.