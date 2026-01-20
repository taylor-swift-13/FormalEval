Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [6; -5; -4; -3; -2; -1; -5; -1] [6].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.