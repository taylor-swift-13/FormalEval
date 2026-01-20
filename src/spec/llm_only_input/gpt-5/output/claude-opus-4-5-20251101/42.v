Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example incr_list_spec_test_empty : incr_list_spec [] [].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.