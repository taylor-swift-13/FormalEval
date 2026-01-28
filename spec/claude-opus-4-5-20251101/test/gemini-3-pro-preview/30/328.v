Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [0; 1; 2; -4; -3; -5; 0; 0; 6; 7; -10; 10; 10; 1; 10; 6; 6] [1; 2; 6; 7; 10; 10; 1; 10; 6; 6].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.