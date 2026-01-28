Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Import ListNotations.

Open Scope nat_scope.
Open Scope string_scope.

Definition total_chars (l : list string) : nat :=
  fold_right (fun s acc => String.length s + acc) 0 l.

Definition total_match_spec (lst1 lst2 res : list string) : Prop :=
  (total_chars lst1 <= total_chars lst2 /\ res = lst1) \/
  (total_chars lst2 < total_chars lst1 /\ res = lst2).

Example test_case : total_match_spec 
  ["LoorecherHijKlrym"; ""; "hcherry"; "datqrstuve"; "LoremWxworldyZ"; "date"; "Lorem"; "date"; ""] 
  ["LoorecherHijKlrym"; ""; "hcherry"; "datqrstuve"; "LoremWxworldyZ"; "date"; "Lorem"; "date"; ""] 
  ["LoorecherHijKlrym"; ""; "hcherry"; "datqrstuve"; "LoremWxworldyZ"; "date"; "Lorem"; "date"; ""].
Proof.
  unfold total_match_spec.
  unfold total_chars.
  simpl.
  left.
  split.
  - apply le_n.
  - reflexivity.
Qed.