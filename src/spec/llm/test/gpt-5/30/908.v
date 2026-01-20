Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => Z.gtb x 0) l.

Example get_positive_spec_test :
  get_positive_spec [0%Z; -1%Z; -2%Z; 0%Z; -9%Z; -3%Z; -6%Z; -4%Z; 9%Z] [9%Z].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.