Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_neg : incr_list_spec [-1; -5; -3; -4; -3; -3] [0; -4; -2; -3; -2; -2].
Proof.
  unfold incr_list_spec.
  reflexivity.
Qed.