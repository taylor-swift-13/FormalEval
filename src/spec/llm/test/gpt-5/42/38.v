Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [0.14907947235135702%R; 0.1%R]
                 [1.14907947235135702%R; 1.1%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2; [|].
  - lra.
  - apply f_equal2; [| reflexivity].
    lra.
Qed.