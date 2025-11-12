
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition correct_bracketing_spec (brackets : string) (result : bool) : Prop :=
  let cnt := fold_left
               (fun acc x =>
                  if x =? "<" then acc + 1
                  else if x =? ">" then acc - 1
                  else acc)
               (list_of_string brackets) 0 in
  result = (cnt =? 0) && (cnt >=? 0).
