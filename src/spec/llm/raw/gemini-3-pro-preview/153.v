
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (n >=? nat_of_ascii "A"%char) && (n <=? nat_of_ascii "Z"%char).

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (n >=? nat_of_ascii "a"%char) && (n <=? nat_of_ascii "z"%char).

Fixpoint strength (s : string) : Z :=
  match s with
  | EmptyString => 0
  | String c s' =>
      let rest := strength s' in
      if is_upper c then 1 + rest
      else if is_lower c then rest - 1
      else rest
  end.

Definition Strongest_Extension_spec (class_name : string) (extensions : list string) (result : string) : Prop :=
  exists (best_ext : string),
    (* The result follows the format ClassName.StrongestExtensionName *)
    result = class_name ++ "." ++ best_ext /\
    (* The chosen extension is in the provided list *)
    In best_ext extensions /\
    (* The chosen extension has the maximum strength *)
    (forall e, In e extensions -> strength e <= strength best_ext) /\
    (* Tie-breaking: If there are multiple with max strength, choose the first one.
       This means there exists a split of the list where best_ext is the pivot,
       and everything before it has strictly less strength. *)
    (exists l1 l2,
       extensions = l1 ++ [best_ext] ++ l2 /\
       forall x, In x l1 -> strength x < strength best_ext).
