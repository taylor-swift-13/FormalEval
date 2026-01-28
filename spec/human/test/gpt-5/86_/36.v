Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Lia.

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


Definition problem_86_pre (s : string) : Prop := True.

Definition  problem_86_spec (s s_out : string) : Prop :=
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

Example anti_shuffle_Raceca_example : problem_86_spec "Raceca" "Raacce".
Proof.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hi_lt c1 c2 Hget1 Hget2.
      destruct i as [| [| [| [| [| [| i']]]]]].
      * simpl in Hget1, Hget2. inversion Hget1; subst. inversion Hget2; subst.
        unfold is_space. split; intro H; exfalso; discriminate H.
      * simpl in Hget1, Hget2. inversion Hget1; subst. inversion Hget2; subst.
        unfold is_space. split; intro H; exfalso; discriminate H.
      * simpl in Hget1, Hget2. inversion Hget1; subst. inversion Hget2; subst.
        unfold is_space. split; intro H; exfalso; discriminate H.
      * simpl in Hget1, Hget2. inversion Hget1; subst. inversion Hget2; subst.
        unfold is_space. split; intro H; exfalso; discriminate H.
      * simpl in Hget1, Hget2. inversion Hget1; subst. inversion Hget2; subst.
        unfold is_space. split; intro H; exfalso; discriminate H.
      * simpl in Hget1, Hget2. inversion Hget1; subst. inversion Hget2; subst.
        unfold is_space. split; intro H; exfalso; discriminate H.
      * simpl in Hget1. discriminate Hget1.
    + exists ["Raceca"], ["Raacce"].
      split.
      * apply sos_base.
        eapply sosar_char.
        -- unfold is_space. intro E. discriminate E.
        -- eapply sosar_char.
           ++ unfold is_space. intro E. discriminate E.
           ++ eapply sosar_char.
              ** unfold is_space. intro E. discriminate E.
              ** eapply sosar_char.
                 --- unfold is_space. intro E. discriminate E.
                 --- eapply sosar_char.
                     +++ unfold is_space. intro E. discriminate E.
                     +++ eapply sosar_char.
                         *** unfold is_space. intro E. discriminate E.
                         *** apply sosar_nil_nonempty. discriminate.
      * split.
        -- apply sos_base.
           eapply sosar_char.
           ++ unfold is_space. intro E. discriminate E.
           ++ eapply sosar_char.
              ** unfold is_space. intro E. discriminate E.
              ** eapply sosar_char.
                 --- unfold is_space. intro E. discriminate E.
                 --- eapply sosar_char.
                     +++ unfold is_space. intro E. discriminate E.
                     +++ eapply sosar_char.
                         *** unfold is_space. intro E. discriminate E.
                         *** eapply sosar_char.
                             ---- unfold is_space. intro E. discriminate E.
                             ---- apply sosar_nil_nonempty. discriminate.
        -- constructor.
           ++ split.
              ** simpl.
                 eapply Permutation_trans.
                 --- apply perm_skip.
                     apply perm_skip.
                     apply perm_skip.
                     apply perm_skip.
                     apply perm_swap.
                 --- eapply Permutation_trans.
                     +++ apply perm_skip.
                         apply perm_skip.
                         apply perm_skip.
                         apply perm_swap.
                     +++ eapply Permutation_trans.
                         *** apply perm_skip.
                             apply perm_skip.
                             apply perm_swap.
                         *** apply perm_skip.
                             apply perm_skip.
                             apply perm_skip.
                             apply perm_skip.
                             apply perm_swap.
              ** eapply sorted_cons with (c2 := "a"%char) (s' := "acce").
                 --- vm_compute. lia.
                 --- eapply sorted_cons with (c2 := "a"%char) (s' := "cce").
                     +++ vm_compute. lia.
                     +++ eapply sorted_cons with (c2 := "c"%char) (s' := "ce").
                         *** vm_compute. lia.
                         *** eapply sorted_cons with (c2 := "c"%char) (s' := "e").
                             ---- vm_compute. lia.
                             ---- eapply sorted_cons with (c2 := "e"%char) (s' := "").
                                  +++++ vm_compute. lia.
                                  +++++ apply sorted_one.
           ++ constructor.
Qed.