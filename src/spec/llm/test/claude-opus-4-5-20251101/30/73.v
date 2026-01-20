Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [-5; 8; 1; -1; 0; 1; 4; -1] [8; 1; 1; 4].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.