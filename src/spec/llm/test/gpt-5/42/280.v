Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_new :
  incr_list_spec [5%Z; 9%Z; 6%Z; 5%Z; 0%Z; 30000%Z; 3%Z; -8%Z; 3%Z]
                 [6%Z; 10%Z; 7%Z; 6%Z; 1%Z; 30001%Z; 4%Z; -7%Z; 4%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.