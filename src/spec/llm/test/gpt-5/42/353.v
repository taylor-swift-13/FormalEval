Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [20%Z; 1%Z; 4%Z; 6%Z; 8%Z; 10%Z; 16%Z; 14%Z; 20%Z; 4%Z]
                 [21%Z; 2%Z; 5%Z; 7%Z; 9%Z; 11%Z; 17%Z; 15%Z; 21%Z; 5%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.