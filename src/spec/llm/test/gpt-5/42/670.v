Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [-10%Z; 10000%Z; 20000%Z; 30000%Z; 40000%Z; 60000%Z; 70000%Z; 80000%Z; 2%Z; 100000%Z; 60000%Z; 10000%Z; 60000%Z; 70000%Z]
    [-9%Z; 10001%Z; 20001%Z; 30001%Z; 40001%Z; 60001%Z; 70001%Z; 80001%Z; 3%Z; 100001%Z; 60001%Z; 10001%Z; 60001%Z; 70001%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.