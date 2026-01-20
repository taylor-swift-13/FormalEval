
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

Definition rotate_string (s : string) (i : nat) : string :=
  substring i (length s - i) s ++ substring 0 i s.

Definition is_substring (needle haystack : string) : Prop :=
  exists prefix suffix, haystack = prefix ++ needle ++ suffix.

Definition is_rotation_substring (a b : string) : Prop :=
  exists i, i < length b /\ is_substring (rotate_string b i) a.

Definition cycpattern_check_spec (a b : string) (result : bool) : Prop :=
  (result = true <->
    (a = b \/
     b = "" \/
     is_rotation_substring a b)).
