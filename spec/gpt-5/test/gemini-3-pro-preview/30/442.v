Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => Z.gtb x 0) l.

Example test_get_positive : get_positive_spec [1; 2; -3; -5; 0; 7; 6; 7; 10; -9; 10] [1; 2; 7; 6; 7; 10; 10].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.