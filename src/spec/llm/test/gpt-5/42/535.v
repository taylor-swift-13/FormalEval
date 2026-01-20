Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [2%Z; 5%Z; 6%Z; 11%Z; 12%Z; 14%Z; 16%Z; 18%Z; 0%Z; 20%Z; 2%Z]
    [3%Z; 6%Z; 7%Z; 12%Z; 13%Z; 15%Z; 17%Z; 19%Z; 1%Z; 21%Z; 3%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.