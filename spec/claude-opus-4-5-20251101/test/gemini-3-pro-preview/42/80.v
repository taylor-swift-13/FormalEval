Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.

Example test_incr_list_complex: incr_list_spec [1; 1; 1; 1; 10; 1; 1; 10] [2; 2; 2; 2; 11; 2; 2; 11].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.