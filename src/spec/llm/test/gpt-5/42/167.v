Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [1%Z; -2%Z; 3%Z; -4%Z; 40000%Z; 9%Z; -10%Z]
                 [2%Z; -1%Z; 4%Z; -3%Z; 40001%Z; 10%Z; -9%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.