Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Fixpoint string_le (s1 s2 : string) : Prop :=
  match s1, s2 with
  | EmptyString, _ => True
  | String _ _, EmptyString => False
  | String c1 s1', String c2 s2' =>
      (nat_of_ascii c1 < nat_of_ascii c2) \/ (c1 = c2 /\ string_le s1' s2')
  end.

Fixpoint string_contains (c : ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c' s' => if Ascii.eqb c c' then true else string_contains c s'
  end.

Fixpoint count_unique_chars (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
      let n := count_unique_chars s' in
      if string_contains c s' then n else S n
  end.

Definition problem_158_spec (words : list string) (result : string) : Prop :=
  In result words /\
  forall w, In w words ->
    let c_res := count_unique_chars result in
    let c_w := count_unique_chars w in
    c_res > c_w \/ (c_res = c_w /\ string_le result w).

(* First, compute the actual counts *)
Lemma count_name : count_unique_chars "name" = 4.
Proof. simpl. reflexivity. Qed.

Lemma count_of : count_unique_chars "of" = 2.
Proof. simpl. reflexivity. Qed.

Lemma count_string : count_unique_chars "string" = 6.
Proof. simpl. reflexivity. Qed.

Example test_find_max : problem_158_spec ["name"; "of"; "string"] "string".
Proof.
  unfold problem_158_spec.
  split.
  - simpl. right. right. left. reflexivity.
  - intros w H.
    destruct H as [H|H].
    + subst w. rewrite count_name, count_string.
      right. split.
      * reflexivity.
      * unfold string_le.
        right. split.
        -- reflexivity.
        -- unfold string_le.
           right. split.
           ++ reflexivity.
           ++ unfold string_le.
              right. split.
              ** reflexivity.
              ** unfold string_le.
                 right. split.
                 --- reflexivity.
                 --- unfold string_le.
                     left. simpl. lia.
    + destruct H as [H|H].
      * subst w. rewrite count_of, count_string.
        left. lia.
      * destruct H as [H|H].
        -- subst w. rewrite count_string.
           right. split.
           ++ reflexivity.
           ++ unfold string_le.
              right. split.
              ** reflexivity.
              ** unfold string_le.
                 right. split.
                 *** reflexivity.
                 *** unfold string_le.
                     right. split.
                     ---- reflexivity.
                     ---- unfold string_le.
                          left. simpl. lia.
        -- contradiction.
Qed.