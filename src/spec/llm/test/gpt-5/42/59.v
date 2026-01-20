Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Lemma incr_list_spec_head_eq :
  4.565252620620896%R = 3.5652526206208957%R + 1%R.
Admitted.

Example incr_list_spec_case :
  incr_list_spec
    [3.5652526206208957%R; 3.7%R; 8.9%R; 1.2%R; 0.5%R]
    [4.565252620620896%R; 4.7%R; 9.9%R; 2.2%R; 1.5%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2 with (f:=@cons R).
  - exact incr_list_spec_head_eq.
  - apply f_equal2 with (f:=@cons R).
    + lra.
    + apply f_equal2 with (f:=@cons R).
      * lra.
      * apply f_equal2 with (f:=@cons R).
        -- lra.
        -- apply f_equal2 with (f:=@cons R).
           ++ lra.
           ++ reflexivity.
Qed.