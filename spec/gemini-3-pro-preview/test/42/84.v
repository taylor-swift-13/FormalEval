Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = map (fun x => x + 1) l.

Example test_incr_list_1 : incr_list_spec [200; 9; 2] [201; 10; 3].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.