Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [10; 2; -4; -5; 0; 6; 2; 2; 6; 6; -9; 10; -5; 2] [10; 2; 6; 2; 2; 6; 6; 10; 2].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.