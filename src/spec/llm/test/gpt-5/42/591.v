Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case1 :
  incr_list_spec
    [1%Z; 10000%Z; 4%Z; 20001%Z; 8%Z; 9999%Z; 20%Z; 50000%Z; 14%Z; 4%Z; 7%Z; 20%Z; 9999%Z]
    [2%Z; 10001%Z; 5%Z; 20002%Z; 9%Z; 10000%Z; 21%Z; 50001%Z; 15%Z; 5%Z; 8%Z; 21%Z; 10000%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.