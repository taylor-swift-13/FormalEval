Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Prime.

Import ListNotations.
Open Scope string_scope.

Definition space : ascii := Ascii.ascii_of_nat 32.

Fixpoint no_space (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c s' => c <> space /\ no_space s'
  end.

Fixpoint join_with_space (ws : list string) : string :=
  match ws with
  | [] => ""
  | w :: [] => w
  | w :: w' :: ws' => w ++ " " ++ join_with_space (w' :: ws')
  end.

Inductive split_by_space : string -> list string -> Prop :=
| sbs_nil :
    split_by_space "" []
| sbs_one w :
    w <> "" ->
    no_space w ->
    split_by_space w [w]
| sbs_cons w s ws :
    w <> "" ->
    no_space w ->
    split_by_space s ws ->
    split_by_space (w ++ " " ++ s) (w :: ws).

Definition prime_length (w : string) : Prop :=
  prime (String.length w).

Inductive filter_subseq (P : string -> Prop) : list string -> list string -> Prop :=
| fs_nil :
    filter_subseq P [] []
| fs_keep x xs ys :
    P x ->
    filter_subseq P xs ys ->
    filter_subseq P (x :: xs) (x :: ys)
| fs_drop x xs ys :
    ~ P x ->
    filter_subseq P xs ys ->
    filter_subseq P (x :: xs) ys.

Definition words_in_sentence_spec (sentence : string) (out : string) : Prop :=
  exists ws ws',
    split_by_space sentence ws /\
    filter_subseq prime_length ws ws' /\
    out = join_with_space ws'.