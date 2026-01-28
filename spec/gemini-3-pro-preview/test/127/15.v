Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition overlap (intervals : list (list Z)) : string :=
  match intervals with
  | [[a; b]; [c; d]] => 
      if (Z.max a c <? Z.min b d) then "YES" else "NO"
  | _ => "NO"
  end.

Example test_overlap: overlap [[1; 5]; [3; 7]] = "YES".
Proof.
  reflexivity.
Qed.