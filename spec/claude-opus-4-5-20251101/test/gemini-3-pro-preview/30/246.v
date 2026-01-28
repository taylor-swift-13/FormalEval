Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [6; 8; -3; 6; -2; -1; 6; -4; -1; 8] [6; 8; 6; 6; 8].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.