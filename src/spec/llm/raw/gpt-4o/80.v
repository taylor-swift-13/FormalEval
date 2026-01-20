
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition is_happy_spec (s : string) (result : bool) : Prop :=
  (length s < 3 -> result = false) /\
  (length s >= 3 ->
    (forall i,
      0 <= i < length s - 2 ->
      (substring i 1 s <> substring (i + 1) 1 s) /\
      (substring i 1 s <> substring (i + 2) 1 s) /\
      (substring (i + 1) 1 s <> substring (i + 2) 1 s)) ->
    result = true) /\
  (exists i,
    0 <= i < length s - 2 /\
    (substring i 1 s = substring (i + 1) 1 s \/
     substring i 1 s = substring (i + 2) 1 s \/
     substring (i + 1) 1 s = substring (i + 2) 1 s) ->
    result = false).
