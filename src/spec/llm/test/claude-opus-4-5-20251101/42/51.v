Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_large : incr_list_spec [1; 10000; 1; 1; 1; 1; 1; 1; 100; 1; 1] [2; 10001; 2; 2; 2; 2; 2; 2; 101; 2; 2].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.