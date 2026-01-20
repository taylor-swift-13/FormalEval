Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [0; 0; 0; 6; 0; 0] [1; 1; 1; 7; 1; 1].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.