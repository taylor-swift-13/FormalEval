Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (l1 l2 : list Z) : string :=
  match l1, l2 with
  | [a; b], [c; d] => 
      if (Z.max a c <? Z.min b d) then "YES" else "NO"
  | _, _ => "NO"
  end.

Example test_intersection: intersection [-10; 1] [-10; 1] = "YES".
Proof. reflexivity. Qed.