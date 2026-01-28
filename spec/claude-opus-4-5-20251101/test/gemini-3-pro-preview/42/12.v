Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_2_2_2_2: incr_list_spec [2; 2; 2; 2] [3; 3; 3; 3].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.