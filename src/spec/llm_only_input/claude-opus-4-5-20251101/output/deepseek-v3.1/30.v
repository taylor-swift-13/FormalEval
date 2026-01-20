Require Import List.
Require Import ZArith.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Z.gtb x 0) l.

Open Scope Z_scope.

Example test_get_positive : get_positive_spec ((-1) :: (-2) :: 4 :: 5 :: 6 :: nil) (4 :: 5 :: 6 :: nil).
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.