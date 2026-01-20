Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition incr_list_spec (l : list Z) (res : list Z) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_test1 :
  incr_list_spec [-40%Z; 80000%Z; 90000%Z; 21%Z; -3%Z; 14%Z; 18%Z; -2%Z; 87%Z]
                 [-39%Z; 80001%Z; 90001%Z; 22%Z; -2%Z; 15%Z; 19%Z; -1%Z; 88%Z].
Proof.
  unfold incr_list_spec.
  simpl.
  reflexivity.
Qed.