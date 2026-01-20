Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = map (fun x => x + 1) l.

Example test_incr_list : incr_list_spec [200; 10; 200] [201; 11; 201].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.