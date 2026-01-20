Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [6; -9; -4; 8; -2; 6; -1; -5; -1; 6] [6; 8; 6; 6].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.