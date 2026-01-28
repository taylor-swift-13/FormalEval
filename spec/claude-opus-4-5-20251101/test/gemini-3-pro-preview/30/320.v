Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [11; 2; -4; -5; 0; 1; 2; 6; 7; -9; 11; 2] [11; 2; 1; 2; 6; 7; 11; 2].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.