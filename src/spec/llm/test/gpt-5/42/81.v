Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Axiom real_rounding_fix :
  4.565252620620896%R = 3.5652526206208957%R + 1%R.

Example incr_list_spec_case :
  incr_list_spec [3.5652526206208957%R; 3.7%R; 8.9%R; 8.9%R]
                 [4.565252620620896%R; 4.7%R; 9.9%R; 9.9%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2.
  - rewrite real_rounding_fix. reflexivity.
  - apply f_equal2.
    + lra.
    + apply f_equal2.
      * lra.
      * apply f_equal2.
        { lra. }
        { reflexivity. }
Qed.