Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_large_numbers :
  incr_list_spec [10%Z; 100%Z; 1000%Z; 10000%Z] [11%Z; 101%Z; 1001%Z; 10001%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.