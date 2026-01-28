Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_1: incr_list_spec [4; -2; -3; -4] [5; -1; -2; -3].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.