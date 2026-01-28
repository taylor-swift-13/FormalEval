Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition filter_spaces (l : list ascii) : list ascii :=
  filter (fun c => if ascii_dec c " "%char then false else true) l.

Definition count_char (letters : list ascii) (c : ascii) : nat :=
  count_occ ascii_dec letters c.

Definition get_max_count (letters : list ascii) : nat :=
  let unique_letters := nodup ascii_dec letters in
  let counts := map (count_char letters) unique_letters in
  fold_right max 0 counts.

Definition problem_111_pre (s : string) : Prop :=
  let letters := list_ascii_of_string s in
  Forall (fun c => c = " "%char \/ let n := nat_of_ascii c in 97 <= n /\ n <= 122) letters.

Definition problem_111_spec (s : string) (res : list (ascii * nat)) : Prop :=
  let raw_letters := list_ascii_of_string s in
  let letters := filter_spaces raw_letters in
  let unique_letters := nodup ascii_dec letters in
  match unique_letters with
  | [] => res = []
  | _ :: _ =>
      let max_count := get_max_count letters in
      (* put parentheses around the conjunction to avoid syntax error *)
      ((forall (p : ascii * nat),
          In p res ->
          let (c, n) := p in
          n = max_count /\ count_char letters c = max_count)
      /\
      (forall c,
          In c unique_letters ->
          count_char letters c = max_count ->
          In (c, max_count) res))
  end.

Example problem_111_example1 :
  problem_111_spec "a b b a" [('a', 2); ('b', 2)].
Proof.
  unfold problem_111_spec.
  set (raw_letters := list_ascii_of_string "a b b a").
  set (letters := filter_spaces raw_letters).
  set (unique_letters := nodup ascii_dec letters).
  destruct unique_letters as [| u1 unique_letters'] eqn:Hunique.
  - discriminate Hunique.
  - set (max_count := get_max_count letters).
    split.
    + (* Soundness *)
      intros [c n] H_in_res.
      simpl in H_in_res.
      destruct H_in_res as [Hc | [Hc | Hnil]].
      * inversion Hc; subst; clear Hc.
        split.
        -- reflexivity.
        -- subst raw_letters letters.
           unfold count_char, count_occ, filter_spaces.
           (* letters = ['a'; 'b'; 'b'; 'a'] *)
           repeat match goal with
           | |- context[count_occ _ ?l ?x] => idtac
           end.
           simpl.
           (* Counting 'a' *)
           reflexivity.
      * inversion Hc; subst; clear Hc.
        split.
        -- reflexivity.
        -- subst raw_letters letters.
           unfold count_char, count_occ, filter_spaces.
           (* Counting 'b' *)
           simpl.
           reflexivity.
      * contradiction.
    + (* Completeness *)
      intros c H_in_unique H_count_eq.
      simpl.
      subst raw_letters letters unique_letters max_count.
      simpl in H_in_unique.
      destruct H_in_unique as [Hc | [Hc | Hfalse]].
      * subst c. simpl. left. reflexivity.
      * destruct Hc.
      * right. left. reflexivity.
Qed.