
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint count_depth_aux (s : list ascii) (cnt : Z) (max_depth : Z) : Z :=
  match s with
  | nil => max_depth
  | ch :: rest =>
    let new_cnt := if Ascii.eqb ch "("%char then cnt + 1
                   else if Ascii.eqb ch ")"%char then cnt - 1
                   else cnt in
    let new_max := Z.max max_depth new_cnt in
    count_depth_aux rest new_cnt new_max
  end.

Definition count_depth (s : list ascii) : Z :=
  count_depth_aux s 0 0.

Fixpoint split_by_space (s : list ascii) (current : list ascii) : list (list ascii) :=
  match s with
  | nil => if (length current =? 0)%nat then nil else [rev current]
  | ch :: rest =>
    if Ascii.eqb ch " "%char then
      if (length current =? 0)%nat then split_by_space rest nil
      else (rev current) :: split_by_space rest nil
    else split_by_space rest (ch :: current)
  end.

Definition parse_nested_parens_spec (paren_string : list ascii) (result : list Z) : Prop :=
  let groups := split_by_space paren_string nil in
  result = map count_depth groups.
