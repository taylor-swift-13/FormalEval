Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Z.gtb x 0) l.

Example get_positive_spec_test :
  get_positive_spec [-1%Z; -2%Z; 4%Z; 5%Z; 6%Z] [4%Z; 5%Z; 6%Z].
Proof.
  unfold get_positive_spec.
  vm_compute.
  reflexivity.
Qed.