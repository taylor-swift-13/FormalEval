Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Bool.Bool.
Import ListNotations.

Inductive exists_in_list {A : Type} : A -> list A -> Prop :=
| eil_head : forall x xs, exists_in_list x (x :: xs)
| eil_tail : forall x y xs, exists_in_list x xs -> exists_in_list x (y :: xs).

Inductive delete_chars_rel : list ascii -> list ascii -> list ascii -> Prop :=
| dcr_nil : forall c, delete_chars_rel nil c nil
| dcr_delete : forall h t c res, @exists_in_list ascii h c ->
    delete_chars_rel t c res ->
    delete_chars_rel (h :: t) c res
| dcr_keep : forall h t c res, ~ @exists_in_list ascii h c ->
    delete_chars_rel t c res ->
    delete_chars_rel (h :: t) c (h :: res).

Inductive is_pal_rel : list ascii -> Prop :=
| ipr_nil : is_pal_rel nil
| ipr_single : forall c, is_pal_rel [c]
| ipr_pair : forall c s, is_pal_rel s -> is_pal_rel (c :: (s ++ [c])).

Definition problem_112_pre (s c : string) : Prop :=
  let ls := list_ascii_of_string s in
  let lc := list_ascii_of_string c in
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) ls /\
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) lc.

Definition problem_112_spec (s c : string) (output : string * bool) : Prop :=
  let '(res, is_pal) := output in
  let ls := list_ascii_of_string s in
  let lc := list_ascii_of_string c in
  let lres := list_ascii_of_string res in
  delete_chars_rel ls lc lres /\
  (is_pal = true <-> is_pal_rel lres).

Example test_example_1 :
  problem_112_spec "abcde" "ae" ("bcd"%string, false).
Proof.
  unfold problem_112_spec.
  simpl.

  (* explicitly rewrite list_ascii_of_string values *)
  change (list_ascii_of_string "abcde") with
    ["a"%char; "b"%char; "c"%char; "d"%char; "e"%char].
  change (list_ascii_of_string "ae") with
    ["a"%char; "e"%char].
  change (list_ascii_of_string ("bcd"%string)) with
    ["b"%char; "c"%char; "d"%char].

  split.
  - (* delete_chars_rel *)
    apply dcr_delete with ("a"%char).
    + apply eil_head.
    + apply dcr_keep with ("b"%char).
      * intro H; inversion H.
      * apply dcr_keep with ("c"%char).
        -- intro H; inversion H.
        -- apply dcr_keep with ("d"%char).
           ++ intro H; inversion H.
           ++ apply dcr_delete with ("e"%char).
              ** apply eil_tail. apply eil_head.
              ** apply dcr_nil.
  - split; intro H.
    + discriminate H.
    + inversion H.
Qed.