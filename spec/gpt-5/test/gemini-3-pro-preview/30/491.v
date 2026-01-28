Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => Z.gtb x 0) l.

Example test_get_positive : get_positive_spec [1; 6; -7; -100; -4; -4; -4; 0; 6; -9; 10; 6; -4] [1; 6; 6; 10; 6].
Proof.
  unfold get_positive_spec.
  (* Simplify the filter function application on the concrete list *)
  simpl.
  (* The simplified term matches the expected result, so we use reflexivity *)
  reflexivity.
Qed.