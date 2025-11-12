
Require Import String.
Require Import List.
Require Import ZArith.

Fixpoint count_consecutive_spaces (s : string) (n : nat) : nat :=
  match s with
  | "" => n
  | String " " rest => count_consecutive_spaces rest (S n)
  | _ => n
  end.

Fixpoint replace_consecutive_spaces (s : string) (max_len : nat) : string :=
  match s with
  | "" => ""
  | String c rest =>
      match c with
      | " " =>
          let n := count_consecutive_spaces rest 1 in
          if n >= max_len then
            "-" ++ replace_consecutive_spaces (substring n rest) max_len
          else
            "_" ++ replace_consecutive_spaces rest max_len
      | _ => String c (replace_consecutive_spaces rest max_len)
      end
  end.

Definition fix_spaces_spec (text : string) (result : string) : Prop :=
  result = replace_consecutive_spaces text 2.
