Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [50001%Z; -3%Z; 6%Z; 2%Z; 20000%Z; 49999%Z; 30000%Z; 12%Z; 50000%Z; 50001%Z; -8%Z; 60000%Z; 70000%Z; 80000%Z; 100000%Z]
    [50002%Z; -2%Z; 7%Z; 3%Z; 20001%Z; 50000%Z; 30001%Z; 13%Z; 50001%Z; 50002%Z; -7%Z; 60001%Z; 70001%Z; 80001%Z; 100001%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.