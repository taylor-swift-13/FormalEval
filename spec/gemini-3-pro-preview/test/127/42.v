Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (interval_1 interval_2 : list Z) : string :=
  match interval_1, interval_2 with
  | [start1; end1], [start2; end2] =>
      let start_inter := Z.max start1 start2 in
      let end_inter := Z.min end1 end2 in
      if start_inter <? end_inter then "YES" else "NO"
  | _, _ => "NO"
  end.

Example test_intersection : intersection [2%Z; 2%Z] [2%Z; 2%Z] = "NO".
Proof.
  reflexivity.
Qed.