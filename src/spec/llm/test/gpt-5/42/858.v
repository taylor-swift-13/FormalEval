Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case_1 :
  incr_list_spec
    [2%Z; 4%Z; 100001%Z; 8%Z; 9999%Z; 10%Z; 20000%Z; 12%Z; 16%Z; 18%Z; 8%Z; 8%Z; 4%Z; 90001%Z; 8%Z; 8%Z; 12%Z]
    [3%Z; 5%Z; 100002%Z; 9%Z; 10000%Z; 11%Z; 20001%Z; 13%Z; 17%Z; 19%Z; 9%Z; 9%Z; 5%Z; 90002%Z; 9%Z; 9%Z; 13%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.