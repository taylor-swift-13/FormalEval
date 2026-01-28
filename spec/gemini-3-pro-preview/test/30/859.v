Require Import Coq.Lists.List.
Require Import Coq.Floats.Floats.
Import ListNotations.
Open Scope float_scope.

Definition get_positive_spec (l : list float) (res : list float) : Prop :=
  res = filter (fun x => 0%float <? x) l.

Example test_get_positive : get_positive_spec 
  [-2.651030586877352; 9.9; 25.221353337136023; 24.93175152910768; -0.42322814636615796; 33.195768044846155; -2.6307909667819085; -2.25] 
  [9.9; 25.221353337136023; 24.93175152910768; 33.195768044846155].
Proof.
  unfold get_positive_spec.
  reflexivity.
Qed.