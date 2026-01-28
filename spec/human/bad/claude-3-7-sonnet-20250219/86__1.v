Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.

Import ListNotations.
Open Scope string_scope.

Definition is_space (c : ascii) : Prop := c = " "%char.

Inductive is_sorted : string -> Prop :=
  | sorted_nil : is_sorted ""
  | sorted_one : forall c, is_sorted (String c "")
  | sorted_cons : forall c1 c2 s',
      nat_of_ascii c1 <= nat_of_ascii c2 ->
      is_sorted (String c2 s') ->
      is_sorted (String c1 (String c2 s')).

Inductive SplitOnSpaces_aux_rel : string -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = "" -> SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group, current_group <> "" -> SplitOnSpaces_aux_rel current_group "" [current_group]
  | sosar_space_empty : forall current_group h t result,
      is_space h ->
      current_group = "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result
  | sosar_space_nonempty : forall current_group h t result,
      is_space h ->
      current_group <> "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) (current_group :: result)
  | sosar_char : forall current_group h t result,
      ~ is_space h ->
      SplitOnSpaces_aux_rel (current_group ++ String h "") t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result.

Inductive SplitOnSpaces_rel : string -> list string -> Prop :=
  | sos_base : forall s result, SplitOnSpaces_aux_rel "" s result -> SplitOnSpaces_rel s result.

Definition list_ascii_of_string (s : string) : list ascii :=
  List.map (fun i => match String.get i s with
                     | Some c => c
                     | None => " "%char (* dummy, should not happen *)
                     end)
           (seq 0 (String.length s)).

Definition problem_86_spec (s s_out : string) : Prop :=
  String.length s = String.length s_out /\
  (forall i, i < String.length s ->
    forall c1 c2,
      String.get i s = Some c1 ->
      String.get i s_out = Some c2 ->
      (is_space c1 <-> is_space c2)) /\
  (exists words_in words_out,
    SplitOnSpaces_rel s words_in /\
    SplitOnSpaces_rel s_out words_out /\
    Forall2 (fun w_in w_out => Permutation (list_ascii_of_string w_in) (list_ascii_of_string w_out) /\ is_sorted w_out) words_in words_out).

(* Lemma that "Hi" contains no spaces *)
Lemma Hi_no_spaces :
  forall i c,
    i < String.length "Hi" ->
    String.get i "Hi" = Some c ->
    ~ is_space c.
Proof.
  intros i c Hi Hget Hspace.
  unfold is_space in Hspace.
  subst.
  (* "Hi" is "H" + "i"; both are not spaces *)
  destruct i; simpl in Hget.
  - inversion Hget; subst.
    discriminate Hspace.
  - destruct i; [|lia]. (* i < length=2 so i=0 or 1 only *)
    inversion Hget; subst.
    discriminate Hspace.
Qed.

(* Prove that "Hi" is sorted *)
Lemma Hi_sorted : is_sorted "Hi".
Proof.
  apply sorted_cons.
  simpl.
  unfold nat_of_ascii.
  lia.
  apply sorted_one.
Qed.

Example example_anti_shuffle_Hi : problem_86_spec "Hi" "Hi".
Proof.
  unfold problem_86_spec.
  repeat split.
  - reflexivity.
  - intros i Hi c1 c2 Hget1 Hget2.
    split; intros H; unfold is_space in *.
    + subst. exfalso.
      apply (Hi_no_spaces i c1 Hi Hget1 H).
    + subst. exfalso.
      apply (Hi_no_spaces i c2 Hi Hget2 H).
  - exists ["Hi"], ["Hi"].
    split.
    + (* SplitOnSpaces_rel "Hi" ["Hi"] *)
      apply sos_base.
      (* By induction on input string *)
      remember "" as cur.
      remember "Hi" as s.
      simpl.
      assert (~ is_space "H"%char) by (unfold is_space; discriminate).
      apply sosar_char with (result := ["Hi"]); try assumption.
      assert (~ is_space "i"%char) by (unfold is_space; discriminate).
      apply sosar_char with (result := ["i"]); try assumption.
      apply sosar_nil_nonempty.
      discriminate.
    + split.
      * (* SplitOnSpaces_rel "Hi" ["Hi"] *)
        apply sos_base.
        remember "" as cur.
        remember "Hi" as s.
        simpl.
        assert (~ is_space "H"%char) by (unfold is_space; discriminate).
        apply sosar_char with (result := ["Hi"]); try assumption.
        assert (~ is_space "i"%char) by (unfold is_space; discriminate).
        apply sosar_char with (result := ["i"]); try assumption.
        apply sosar_nil_nonempty.
        discriminate.
      * (* Forall2 property *)
        constructor.
        -- split.
           ++ (* Permutation of list_ascii_of_string *)
              unfold list_ascii_of_string.
              simpl.
              (* list_ascii_of_string "Hi" = ["H";"i"] *)
              apply Permutation_refl.
           ++ (* is_sorted "Hi" *)
              apply Hi_sorted.
        -- constructor.
Qed.