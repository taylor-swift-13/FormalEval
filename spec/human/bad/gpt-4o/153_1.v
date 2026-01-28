(* Required imports *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z_scope.

(* Auxiliary functions *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

(* Check if a character is uppercase *)
Definition is_uppercase (c : ascii) : bool :=
  ("A" <=? c)%char && (c <=? "Z")%char.

(* Check if a character is lowercase *)
Definition is_lowercase (c : ascii) : bool :=
  ("a" <=? c)%char && (c <=? "z")%char.

(* Count characters satisfying a predicate *)
Definition count_pred (p : ascii -> bool) (s : list ascii) : nat :=
  length (filter p s).

(* Calculate the strength of an extension *)
Definition strength (s : string) : Z :=
  let l := list_ascii_of_string s in
  Z.of_nat (count_pred is_uppercase l) - Z.of_nat (count_pred is_lowercase l).

(* Predicate for strongest extension *)
Definition is_strongest (best : string) (exts : list string) : Prop :=
  exists prefix post,
    exts = prefix ++ [best] ++ post /\
    ~ In best prefix /\
    (forall e, In e prefix -> (strength e < strength best)%Z) /\
    (forall e, In e post -> (strength e <= strength best)%Z).

(* Precondition: extensions list must be non-empty *)
Definition problem_153_pre (class_name : string) (extensions : list string) : Prop :=
  extensions <> [].

(* Specification *)
Definition problem_153_spec (class_name : string) (extensions : list string) (res : string) : Prop :=
  match extensions with
  | [] => False
  | _ :: _ =>
      exists strongest_ext,
        is_strongest strongest_ext extensions /\
        res = class_name ++ "." ++ strongest_ext
  end.

(* Test case proof *)
Example test_problem_153:
  problem_153_spec "Watashi" ["tEN"; "niNE"; "eIGHt8OKe"] "Watashi.eIGHt8OKe".
Proof.
  unfold problem_153_spec.
  exists "eIGHt8OKe".
  split.
  - unfold is_strongest.
    exists ["tEN"; "niNE"], [].
    split.
    + reflexivity.
    + split.
      * simpl. intuition.
      * split.
        -- intros e [H | [H | []]]; unfold strength; simpl; lia.
        -- intros e []. 
  - reflexivity.
Qed.