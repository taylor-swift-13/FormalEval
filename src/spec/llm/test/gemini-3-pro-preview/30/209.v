Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [-1; -3; -5; -3; -4; 6; 0; 6; 7; -9; 10; 5; 10; -9] [6; 6; 7; 10; 5; 10].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.