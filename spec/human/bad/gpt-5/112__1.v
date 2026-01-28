Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Bool.Bool.
Import ListNotations.
Local Open Scope string_scope.

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

Lemma exists_in_list_nil : forall (A : Type) (x : A), ~ exists_in_list x (@nil A).
Proof.
  intros A x H. inversion H.
Qed.

Lemma not_in_cons {A : Type} (x y : A) (xs : list A) :
  x <> y -> ~ exists_in_list x xs -> ~ exists_in_list x (y :: xs).
Proof.
  intros Hxy Hxs H.
  inversion H; subst.
  - contradiction.
  - apply Hxs; assumption.
Qed.

Example problem_112_spec_example_abcde_ae :
  problem_112_spec "abcde" "ae" ("bcd"%string, false).
Proof.
  unfold problem_112_spec.
  simpl.
  split.
  - (* delete_chars_rel proof *)
    eapply dcr_delete.
    + (* 'a' is in ["a";"e"] *)
      apply eil_head.
    + (* process ["b";"c";"d";"e"] to ["b";"c";"d"] *)
      eapply dcr_keep.
      * (* 'b' not in ["a";"e"] *)
        apply not_in_cons.
        -- intro Heq. congruence.
        -- apply not_in_cons.
           ++ intro Heq. congruence.
           ++ apply exists_in_list_nil.
      * (* process ["c";"d";"e"] to ["c";"d"] *)
        eapply dcr_keep.
        -- (* 'c' not in ["a";"e"] *)
           apply not_in_cons.
           ++ intro Heq. congruence.
           ++ apply not_in_cons.
              ** intro Heq. congruence.
              ** apply exists_in_list_nil.
        -- (* process ["d";"e"] to ["d"] *)
           eapply dcr_keep.
           ++ (* 'd' not in ["a";"e"] *)
              apply not_in_cons.
              ** intro Heq. congruence.
              ** apply not_in_cons.
                 --- intro Heq. congruence.
                 --- apply exists_in_list_nil.
           ++ (* process ["e"] to [] *)
              eapply dcr_delete.
              ** (* 'e' is in ["a";"e"] *)
                 apply (eil_tail "e"%char "a"%char ["e"%char]).
                 apply eil_head.
              ** (* base case *)
                 apply dcr_nil.
  - (* palindrome equivalence: false = true <-> is_pal_rel ["b";"c";"d"] *)
    split.
    + intro H. discriminate H.
    + intros Hpal.
      exfalso.
      inversion Hpal; subst.
      * discriminate.
      * discriminate.
      * (* pair case: ["b";"c";"d"] = c :: (s ++ [c]) *)
        inversion H1; subst.
        (* Now we have: ["c";"d"] = s ++ ["b"] *)
        clear H3.
        destruct s as [| sh st].
        -- simpl in H2. discriminate.
        -- simpl in H2.
           inversion H2; subst.
           (* Now: ["d"] = st ++ ["b"] *)
           clear H4.
           destruct st as [| st1 st2].
           ++ simpl in H5. inversion H5; subst. congruence.
           ++ simpl in H5. inversion H5.
Qed.