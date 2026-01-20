Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example test_get_positive : get_positive_spec [0; -4; 2.5; 5; -2.2; -8; 7.7; 9.9; -10.5; 7.7] [2.5; 5; 7.7; 9.9; 7.7].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (destruct Rlt_dec; try lra).
  reflexivity.
Qed.