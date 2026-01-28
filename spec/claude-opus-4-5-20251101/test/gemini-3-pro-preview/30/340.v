Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [-1; -2; -5; -3; 6; 6; 7; -9; 6; 5; 10; -9] [6; 6; 7; 6; 5; 10].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.