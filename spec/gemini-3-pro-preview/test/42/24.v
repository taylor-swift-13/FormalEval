Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = map (fun x => x + 1) l.

Example test_incr_list_1 : incr_list_spec [10; 100; 1000; 10] [11; 101; 1001; 11].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.