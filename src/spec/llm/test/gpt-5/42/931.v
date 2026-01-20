Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [-2%Z; 3%Z; -1%Z; 90001%Z; 0%Z; 10%Z; 20%Z; -5%Z; 1%Z; -2%Z; -7%Z; 10%Z; 3%Z; 10%Z; 10%Z]
    [-1%Z; 4%Z; 0%Z; 90002%Z; 1%Z; 11%Z; 21%Z; -4%Z; 2%Z; -1%Z; -6%Z; 11%Z; 4%Z; 11%Z; 11%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.