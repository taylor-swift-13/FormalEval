Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Inductive exists_in_list {A : Type} : A -> list A -> Prop :=
| eil_head : forall x xs, exists_in_list x (x :: xs)
| eil_tail : forall x y xs, exists_in_list x xs -> exists_in_list x (y :: xs).

Inductive delete_chars_rel : list ascii -> list ascii -> list ascii -> Prop :=
| dcr_nil : forall c, delete_chars_rel nil c nil
| dcr_delete : forall h t c res, exists_in_list h c ->
    delete_chars_rel t c res ->
    delete_chars_rel (h :: t) c res
| dcr_keep : forall h t c res, ~ exists_in_list h c ->
    delete_chars_rel t c res ->
    delete_chars_rel (h :: t) c (h :: res).

Inductive is_pal_rel : list ascii -> Prop :=
| ipr_nil : is_pal_rel nil
| ipr_single : forall c, is_pal_rel [c]
| ipr_pair : forall c s, is_pal_rel s -> is_pal_rel (c :: (s ++ [c])).

(* s and c only contain lowercase letters *)
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

Example test_problem_112 : problem_112_spec "abcde" "ae" ("bcd", false).
Proof.
  unfold problem_112_spec.
  simpl.
  split.
  - (* Prove delete_chars_rel *)
    (* 'a' is in "ae", delete it *)
    apply dcr_delete.
    { apply eil_head. }
    (* 'b' is not in "ae", keep it *)
    apply dcr_keep.
    { intro H. inversion H; subst. discriminate. inversion H2; subst. discriminate. inversion H4. }
    (* 'c' is not in "ae", keep it *)
    apply dcr_keep.
    { intro H. inversion H; subst. discriminate. inversion H2; subst. discriminate. inversion H4. }
    (* 'd' is not in "ae", keep it *)
    apply dcr_keep.
    { intro H. inversion H; subst. discriminate. inversion H2; subst. discriminate. inversion H4. }
    (* 'e' is in "ae", delete it *)
    apply dcr_delete.
    { apply eil_tail. apply eil_head. }
    (* End of string *)
    apply dcr_nil.

  - (* Prove is_pal_rel check: false <-> is_pal_rel "bcd" *)
    split; intro H.
    + (* false = true -> False *)
      discriminate H.
    + (* is_pal_rel "bcd" -> False *)
      (* "bcd" is ['b'; 'c'; 'd'] *)
      inversion H; subst.
      * (* ipr_nil: "bcd" is not nil *) discriminate.
      * (* ipr_single: "bcd" length is not 1 *) discriminate.
      * (* ipr_pair: "bcd" = c :: s ++ [c] *)
        (* This implies head 'b' must equal last 'd', which is false *)
        destruct s.
        { (* s is empty, "bcd" = [c; c] -> length 3 vs 2 *)
          simpl in H2. inversion H2.
        }
        { (* s is x :: xs *)
          simpl in H2. inversion H2; subst.
          (* We have: xs ++ [b] = [d] *)
          destruct s.
          { (* xs is empty: [b] = [d] -> b = d -> False *)
            simpl in H4. inversion H4; subst. discriminate.
          }
          { (* xs is y :: ys: length mismatch *)
            simpl in H4. inversion H4. destruct s; inversion H5.
          }
        }
Qed.