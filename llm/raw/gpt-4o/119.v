
Require Import List.
Require Import String.

Definition valid_parens (s : string) : bool :=
  let fix aux (s : string) (cnt : nat) : bool :=
      match s with
      | EmptyString => cnt =? 0
      | String ch s' =>
        let cnt' := if ch = "(" then cnt + 1 else cnt - 1 in
        if cnt' <? 0 then false else aux s' cnt'
      end
  in aux s 0.

Definition match_parens_spec (lst : list string) (result : string) : Prop :=
  length lst = 2 /\
  (result = "Yes" <-> valid_parens (hd "" lst ++ nth 1 lst "") = true \/ valid_parens (nth 1 lst "" ++ hd "" lst) = true) /\
  (result = "No" <-> ~(valid_parens (hd "" lst ++ nth 1 lst "") = true \/ valid_parens (nth 1 lst "" ++ hd "" lst) = true)).
