Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [-1; -2; -5; -3; 8; -4; 6; 0; 11; -6; -9; 10; 7; 7] [8; 6; 11; 10; 7; 7].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.