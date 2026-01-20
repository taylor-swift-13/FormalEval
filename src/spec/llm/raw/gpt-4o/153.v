
Require Import List.
Require Import String.
Require Import Ascii.

Definition strength (s : string) : Z :=
  let fix count_chars (s : string) (cap sm : Z) : Z :=
    match s with
    | EmptyString => cap - sm
    | String c s' =>
      if is_upper c then count_chars s' (cap + 1) sm
      else if is_lower c then count_chars s' cap (sm + 1)
      else count_chars s' cap sm
    end
  in count_chars s 0 0.

Definition Strongest_Extension_spec (class_name : string) (extensions : list string) (result : string) : Prop :=
  exists strongest_extension,
    In strongest_extension extensions /\
    (forall e, In e extensions -> strength e <= strength strongest_extension) /\
    (forall e, In e extensions -> strength e = strength strongest_extension -> nth_error extensions (index strongest_extension extensions) <= nth_error extensions (index e extensions)) /\
    result = class_name ++ "." ++ strongest_extension.

