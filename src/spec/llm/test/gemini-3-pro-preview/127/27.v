Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [[a; b]; [c; d]] =>
      let start_inter := Z.max a c in
      let end_inter := Z.min b d in
      if start_inter <? end_inter then "YES" else "NO"
  | _ => "NO"
  end.

Example test_intersection : intersection [[5%Z; 5%Z]; [5%Z; 5%Z]] = "NO".
Proof.
  compute.
  reflexivity.
Qed.