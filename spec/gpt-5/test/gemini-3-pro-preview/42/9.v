Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_basic : incr_list_spec [10; 100; 1000; 10000] [11; 101; 1001; 10001].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.