
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_substring (sub str : string) : Prop :=
  exists prefix suffix, str = prefix ++ sub ++ suffix.

Fixpoint rotate (s : string) (n : nat) : string :=
  let len := String.length s in
  if len =? 0 then s else
  let n' := n mod len in
  substring n' (len - n') s ++ substring 0 n' s.

Definition cycpattern_check_spec (a b : string) (res : bool) : Prop :=
  res = true <->
    (a = b) \/ (b = "") \/ 
    (exists i, i < String.length b /\ is_substring (rotate b i) a).
