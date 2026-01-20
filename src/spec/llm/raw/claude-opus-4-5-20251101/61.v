
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint check_brackets_aux (chars : list ascii) (cnt : Z) : bool :=
  match chars with
  | nil => Z.eqb cnt 0
  | c :: rest =>
    let new_cnt := if Ascii.eqb c "("%char then cnt + 1
                   else if Ascii.eqb c ")"%char then cnt - 1
                   else cnt in
    if Z.ltb new_cnt 0 then false
    else check_brackets_aux rest new_cnt
  end.

Definition correct_bracketing_spec (brackets : string) (result : bool) : Prop :=
  let chars := list_ascii_of_string brackets in
  result = check_brackets_aux chars 0.
