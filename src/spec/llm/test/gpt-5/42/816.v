Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [-0.694286281155515%R; 3.8%R; -2.1%R; 3.2%R; 7.9%R; -0.5%R; -0.5%R; 3.2%R; -0.7414188614596702%R; 7.9%R; -0.694286281155515%R]
    (List.map (fun x => x + 1)
      [-0.694286281155515%R; 3.8%R; -2.1%R; 3.2%R; 7.9%R; -0.5%R; -0.5%R; 3.2%R; -0.7414188614596702%R; 7.9%R; -0.694286281155515%R]).
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.