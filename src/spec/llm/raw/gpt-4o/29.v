
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Definition filter_by_prefix_spec (strings : list string) (prefix : string) (filtered : list string) : Prop :=
  filtered = filter (fun x => string_prefix prefix x) strings.

Definition string_prefix (prefix str : string) : bool :=
  match prefix, str with
  | "", _ => true
  | _, "" => false
  | String a s1, String b s2 => if Ascii.eqb a b then string_prefix s1 s2 else false
  end.
