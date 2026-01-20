Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_large : incr_list_spec [2; 200; 2; 2; 10000; 2] [3; 201; 3; 3; 10001; 3].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.