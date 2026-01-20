Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => x >? 0) l.

Example test_get_positive : get_positive_spec [10; -10; 15; -3; 20; -20; 25; -20; -5] [10; 15; 20; 25].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.