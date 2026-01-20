
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition count_distinct_characters_spec (string : string) (count : Z) : Prop :=
  let lower_string := map Ascii.to_lower (list_ascii_of_string string) in
  count = Z.of_nat (length (nodup ascii_dec lower_string)).
