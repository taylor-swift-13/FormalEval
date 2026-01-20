Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [-78%Z; -17%Z; 90%Z; 16%Z; -35%Z; -6%Z; -8%Z; 4%Z; 49%Z; 40001%Z]
                 [-77%Z; -16%Z; 91%Z; 17%Z; -34%Z; -5%Z; -7%Z; 5%Z; 50%Z; 40002%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.