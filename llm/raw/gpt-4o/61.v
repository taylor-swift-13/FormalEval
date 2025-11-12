
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition correct_bracketing_spec (brackets : string) (result : bool) : Prop :=
  exists cnt : nat,
    (forall i : nat,
        i < String.length brackets ->
        (substring i 1 brackets = "(" -> cnt = cnt + 1) /\
        (substring i 1 brackets = ")" -> cnt = cnt - 1) /\
        (cnt < 0 -> result = false)) /\
    (cnt = 0 -> result = true).
