Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [-5; -4; -1; 0; 1; 4; 5] [1; 4; 5].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.