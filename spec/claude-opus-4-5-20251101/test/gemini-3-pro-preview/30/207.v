Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [1; 2; 3; -4; -5; 0; 6; -9; -5; 10; -9] [1; 2; 3; 6; 10].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.