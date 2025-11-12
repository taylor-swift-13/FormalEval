
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_rotation (s1 s2 : string) : Prop :=
  exists n, s2 = substring n (length s2 - n) s1 ++ substring 0 n s1.

Definition cycpattern_check_spec (a b : string) (result : bool) : Prop :=
  (a = b \/ b = "" \/ exists s, is_rotation b s /\ substring 0 (length s) a = s) <-> result = true.
