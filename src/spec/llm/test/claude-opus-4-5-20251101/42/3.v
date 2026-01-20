Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [5; 2; 5; 2; 3; 3; 9; 0; 123] [6; 3; 6; 3; 4; 4; 10; 1; 124].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.