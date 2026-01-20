Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case1 :
  incr_list_spec
    [80000%Z; -2%Z; 3%Z; -4%Z; 40000%Z; 12%Z; 9%Z; 3%Z]
    [80001%Z; -1%Z; 4%Z; -3%Z; 40001%Z; 13%Z; 10%Z; 4%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.