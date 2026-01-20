Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_nonempty :
  incr_list_spec
    [4%Z; 4%Z; 60001%Z; 8%Z; 3%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; -6%Z; 8%Z; 8%Z; 4%Z; 4%Z]
    [5%Z; 5%Z; 60002%Z; 9%Z; 4%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; -5%Z; 9%Z; 9%Z; 5%Z; 5%Z].
Proof.
  unfold incr_list_spec.
  vm_compute.
  reflexivity.
Qed.