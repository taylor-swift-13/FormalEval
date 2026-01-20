Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_test :
  incr_list_spec
    [10000%Z; 20000%Z; -10%Z; 40000%Z; 15%Z; 70000%Z; 79999%Z; 90000%Z; 100000%Z]
    [10001%Z; 20001%Z; -9%Z; 40001%Z; 16%Z; 70001%Z; 80000%Z; 90001%Z; 100001%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.