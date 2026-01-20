Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [7%Z; -5%Z; 8%Z; 9%Z; 20000%Z; -1%Z; 9%Z; 20000%Z]
                 [8%Z; -4%Z; 9%Z; 10%Z; 20001%Z; 0%Z; 10%Z; 20001%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.