Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => Z.gtb x 0) l.

Example test_get_positive : get_positive_spec [10; 15; -3; 20; -20; 8; -25; 20] [10; 15; 20; 8; 20].
Proof.
  unfold get_positive_spec.
  (* Simplify the filter function application on the concrete list *)
  simpl.
  (* The simplified term matches the expected result, so we use reflexivity *)
  reflexivity.
Qed.