Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [-3.4; -2; -0.5; 0; 3.2; 5.9; 8.6; 5.9]
                 [-2.4; -1; 0.5; 1; 4.2; 6.9; 9.6; 6.9].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2 with (f:=@cons R); [lra|].
  apply f_equal2 with (f:=@cons R); [lra|].
  apply f_equal2 with (f:=@cons R); [lra|].
  apply f_equal2 with (f:=@cons R); [lra|].
  apply f_equal2 with (f:=@cons R); [lra|].
  apply f_equal2 with (f:=@cons R); [lra|].
  apply f_equal2 with (f:=@cons R); [lra|].
  apply f_equal2 with (f:=@cons R); [lra| reflexivity].
Qed.