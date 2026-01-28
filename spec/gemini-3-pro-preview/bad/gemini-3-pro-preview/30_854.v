Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_positive (x : R) : bool :=
  if Rlt_dec 0 x then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_positive l.

Example test_get_positive : get_positive_spec 
  [0.5; 0; 10.538283343362641; 24.93175152910768; -4; 2.5; 5; -2.2; -2.651030586877352; -8; 7.7; 9.9; -10.5; 9.9; -8; 7.7] 
  [0.5; 10.538283343362641; 24.93175152910768; 2.5; 5; 7.7; 9.9; 9.9; 7.7].
Proof.
  unfold get_positive_spec, is_positive.
  simpl.
  repeat (match goal with
          | |- context [Rlt_dec 0 ?x] => 
              destruct (Rlt_dec 0 x); try lra
          end).
  reflexivity.
Qed.