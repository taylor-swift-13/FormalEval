Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [-8%Z; 40000%Z; 5%Z; 9%Z; -2%Z; 6%Z; 6%Z; 0%Z; -1%Z; -8%Z; 3%Z; -1%Z; 9%Z; 0%Z]
    [-7%Z; 40001%Z; 6%Z; 10%Z; -1%Z; 7%Z; 7%Z; 1%Z; 0%Z; -7%Z; 4%Z; 0%Z; 10%Z; 1%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.