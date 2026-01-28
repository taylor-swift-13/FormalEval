Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_1: incr_list_spec [2%Z; -1%Z; 500%Z] [3%Z; 0%Z; 501%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.