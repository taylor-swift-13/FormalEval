Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec [40000%Z; 70000%Z; 60001%Z; -10%Z; 60000%Z; -5%Z; 7%Z; 20%Z; 20000%Z; 60000%Z; 60001%Z]
                 [40001%Z; 70001%Z; 60002%Z; -9%Z; 60001%Z; -4%Z; 8%Z; 21%Z; 20001%Z; 60001%Z; 60002%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.