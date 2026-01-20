Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_pos_bool (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_pos_bool l.

Example test_get_positive : get_positive_spec 
  [1/2; 0; 5/2; 5; -11/5; -8; -3/4; 77/10; 99/10; -21/2; 5; -8] 
  [1/2; 5/2; 5; 77/10; 99/10; 5].
Proof.
  unfold get_positive_spec, is_pos_bool.
  simpl.
  repeat (destruct (Rgt_dec _ _) as [H|H]; [ try (exfalso; lra) | try (exfalso; lra) ]; simpl).
  reflexivity.
Qed.