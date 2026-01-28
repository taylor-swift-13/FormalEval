Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_1: incr_list_spec [-1; -3; -5; -5] [0; -2; -4; -4].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.