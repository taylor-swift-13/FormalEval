
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Definition flip_case_spec (string : string) (result : string) : Prop :=
  result = String.concat "" (map (fun x => if (x <? "a"%char || x >? "z"%char) && (x <? "A"%char || x >? "Z"%char) then x else if x <? "a"%char then x + 32 else x - 32) (list_of_string string)).
