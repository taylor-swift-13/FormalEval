Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Bool.
Require Import Lia.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.
Open Scope Z_scope.

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

Definition is_uppercase (c : ascii) : bool :=
  ("A" <=? c)%char && (c <=? "Z")%char.

Definition is_lowercase (c : ascii) : bool :=
  ("a" <=? c)%char && (c <=? "z")%char.

Definition count_pred (p : ascii -> bool) (s : list ascii) : nat :=
  length (filter p s).

Definition strength (s : string) : Z :=
  let l := list_ascii_of_string s in
  Z.of_nat (count_pred is_uppercase l) - Z.of_nat (count_pred is_lowercase l).

Definition is_strongest (best : string) (exts : list string) : Prop :=
  exists prefix post,
    exts = prefix ++ best :: post /\
    ~ In best prefix /\
    ((forall e, In e prefix -> (strength e < strength best)%Z) /\
     (forall e, In e post -> (strength e <= strength best)%Z)).

Definition problem_153_pre (class_name : string) (extensions : list string) : Prop :=
  extensions <> [].

Definition problem_153_spec (class_name : string) (extensions : list string) (res : string) : Prop :=
  match extensions with
  | [] => False
  | _ :: _ =>
      exists strongest_ext,
        is_strongest strongest_ext extensions /\
        res = class_name ++ "." %string ++ strongest_ext
  end.

Example problem_153_example_watashi :
  problem_153_spec "Watashi" ["tEN"; "niNE"; "eIGHt8OKe"] "Watashi.eIGHt8OKe".
Proof.
  unfold problem_153_spec; simpl.
  exists "eIGHt8OKe".
  split.
  - unfold is_strongest.
    exists ["tEN"; "niNE"], (@nil string).
    split; [reflexivity|].
    split.
    + intro H; simpl in H; destruct H as [H|[H|[]]]; congruence.
    + split.
      * intros e H.
        assert (strength "tEN" = 1%Z) as Ht by (unfold strength; simpl; compute; reflexivity).
        assert (strength "niNE" = 0%Z) as Hn by (unfold strength; simpl; compute; reflexivity).
        assert (strength "eIGHt8OKe" = 2%Z) as He by (unfold strength; simpl; compute; reflexivity).
        simpl in H; destruct H as [H|[H|[]]]; subst; rewrite ?Ht, ?Hn, ?He; lia.
      * intros e H; simpl in H; contradiction.
  - simpl; reflexivity.
Qed.