
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint is_substring (sub s : string) : bool :=
  match s with
  | EmptyString => 
      match sub with
      | EmptyString => true
      | _ => false
      end
  | String c rest =>
      if string_dec sub EmptyString then true
      else if prefix sub s then true
      else is_substring sub rest
  end
with prefix (sub s : string) : bool :=
  match sub with
  | EmptyString => true
  | String c1 rest1 =>
      match s with
      | EmptyString => false
      | String c2 rest2 =>
          if Ascii.eqb c1 c2 then prefix rest1 rest2
          else false
      end
  end.

Definition filter_by_substring_spec (strings : list string) (substring : string) (result : list string) : Prop :=
  result = filter (fun s => is_substring substring s) strings.
