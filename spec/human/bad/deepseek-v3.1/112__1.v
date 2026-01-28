Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Bool.Bool.
Import ListNotations.

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

(* s 与 c 仅包含小写字母 *)
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

(* Additional helper lemma to relate string literals to list of ascii *)
Lemma string_to_list_eq : list ascii := ["b";"c";"d"].
Proof.
  reflexivity.
Qed.

(* Full proof of the test case *)
Lemma test_case: 
  problem_112_pre "abcde" "ae" /\
  problem_112_spec "abcde" "ae" ("bcd", false).
Proof.
  split.
  - (* Precondition *)
    unfold problem_112_pre; simpl.
    split; 
    try (apply Forall_cons; [apply Forall_nil |]; simpl; [lia | lia]).
    + (* ls: "abcde" *)
      repeat constructor.
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
      * simpl; lia.
    + (* lc: "ae" *)
      repeat constructor.
      * simpl; lia.
      * simpl; lia.
  - (* Specification *)
    unfold problem_112_spec; simpl.
    split.
    + (* delete_chars_rel relation for "abcde" and "ae" -> "bcd" *)
      (* Construct the delete relation explicitly *)
      assert (Hls: list ascii := ["a";"b";"c";"d";"e"]) by reflexivity.
      assert (Hlc: list ascii := ["a";"e"]) by reflexivity.
      (* Remove "a" *)
      eapply dcr_delete; [apply eil_head |].
      (* Remaining list: "b";"c";"d";"e" *)
      eapply dcr_keep; [|]
      ; try (apply eil_tail; apply eil_head).
      (* Remove "e" from remaining list *)
      eapply dcr_delete; [apply eil_tail; apply eil_head |].
      + (* base case with "b";"c";"d" *)
        apply eil_tail; apply eil_tail; apply eil_head.
      + (* Final list *)
        apply dcr_nil.
    + (* Check if res is palindrome: "bcd" *)
      simpl.
      split; [discriminate|].
      intros H.
      (* The list "b";"c";"d" satisfies the is_pal_rel structure (not necessarily a palindrome) *)
      destruct H as [Hrel1 Hrel2].
      (* Show that "b";"c";"d" is not a palindrome, so is_pal = false *)
      simpl in Hrel2.
      discriminate.
Qed.