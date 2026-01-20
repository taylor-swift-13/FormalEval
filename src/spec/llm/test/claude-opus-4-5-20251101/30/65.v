Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [1; -1; 2; -2; -3; 4; -4; 0; 1] [1; 2; 4; 1].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.