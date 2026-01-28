Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [10; 2; -4; -5; 0; 2; 2; 6; 6; -9; 10; -5] [10; 2; 2; 2; 6; 6; 10].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.