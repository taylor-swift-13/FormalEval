Require Import List Ascii String.
Require Import Bool.
Open Scope string_scope.

Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example test_same_chars_1 : problem_54_spec "eabcdzzzz" "dddzzzzzzzddeddabc" true.
Proof.
  unfold problem_54_spec. simpl.
  split.
  - intros _. intros c.
    split; intros H.
    + (* c in s0 -> c in s1 *)
      simpl in H.
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
      * rewrite <- H. simpl.
        right; right; right; right; right; right; right; right; right;
        right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; right; right; right; right;
        right; right; right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; right; right; right; right;
        right; right; right; right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; right; right; right; right;
        right; right; right; right; right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl. left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; left; reflexivity.
      * contradiction.
    + (* c in s1 -> c in s0 *)
      simpl in H.
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]].
      * rewrite <- H. simpl.
        right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; left; reflexivity.
      * rewrite <- H. simpl.
        right; right; right; left; reflexivity.
      * contradiction.
  - intros _. reflexivity.
Qed.