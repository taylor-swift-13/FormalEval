Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => Z.gtb x 0) l.

Example test_get_positive : get_positive_spec ((-1)%Z :: (-2)%Z :: 4%Z :: 5%Z :: 6%Z :: nil) (4%Z :: 5%Z :: 6%Z :: nil).
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.