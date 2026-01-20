Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [6; -5; 11; -1; -3; -4; -1; -5; -1; 11] [6; 11; 11].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.