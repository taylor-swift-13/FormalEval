Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_test1 :
  incr_list_spec [3%Z; -1%Z; 6%Z; 0%Z; 10%Z; 9%Z; 6%Z; -2%Z; -7%Z; 6%Z]
                 [4%Z; 0%Z; 7%Z; 1%Z; 11%Z; 10%Z; 7%Z; -1%Z; -6%Z; 7%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.