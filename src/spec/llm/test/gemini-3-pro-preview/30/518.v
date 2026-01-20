Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [-1; -2; -2; -5; -3; 2; -4; 6; -9; 6; 7; -9] [2; 6; 6; 7].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.