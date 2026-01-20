Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_empty :
  incr_list_spec [-0.5%R; 3.8%R; -2.1%R; 3.2%R; 9.406367499891232%R; 3.2%R]
                 [0.5%R; 4.8%R; -1.1%R; 4.2%R; 10.406367499891232%R; 4.2%R].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat (apply (f_equal2 (@cons R)); [lra |]).
  reflexivity.
Qed.