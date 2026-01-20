Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [10; 15; -3; 20; -20; 8; -25; 20] [10; 15; 20; 8; 20].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.