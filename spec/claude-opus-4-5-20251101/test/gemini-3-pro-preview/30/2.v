Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [5; 3; -5; 2; 3; 3; 9; 0; 123; 1; -10] [5; 3; 2; 3; 3; 9; 123; 1].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.