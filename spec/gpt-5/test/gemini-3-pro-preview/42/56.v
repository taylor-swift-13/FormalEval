Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [1; 2; 3; 4; 5; 6; 5] [2; 3; 4; 5; 6; 7; 6].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.