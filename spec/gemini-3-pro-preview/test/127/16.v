Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (interval_1 : list Z) (interval_2 : list Z) : string :=
  match interval_1, interval_2 with
  | [a; b], [c; d] => 
      let start := Z.max a c in
      let finish := Z.min b d in
      if start <? finish then "YES" else "NO"
  | _, _ => "NO"
  end.

Example test_case: intersection [-6; -2] [-1; 1] = "NO".
Proof.
  reflexivity.
Qed.