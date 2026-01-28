Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_neg : incr_list_spec [-1; -3; -4; -5; -1] [0; -2; -3; -4; 0].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.