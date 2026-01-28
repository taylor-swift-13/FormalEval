Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [-1; 2; -9; -4; -4; 7; -100; 1; 0; 2] [2; 7; 1; 2].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.