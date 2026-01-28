Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [-2; 10; -4; 6; 0; 6; 7; -9; 10; -3] [10; 6; 6; 7; 10].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.