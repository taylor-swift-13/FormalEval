Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool Coq.micromega.Lia.
Import ListNotations.

Inductive has_divisor_from_rel : nat -> nat -> Prop :=
| hdfr_base : forall n d, n mod d = 0 -> d > 1 -> has_divisor_from_rel n d
| hdfr_step : forall n d, has_divisor_from_rel n (S d) -> has_divisor_from_rel n d.

Inductive is_prime_rel : nat -> Prop :=
| ipr_prime : forall n, n > 1 -> ~ (exists d, 2 <= d <= n - 1 /\ has_divisor_from_rel n d) ->
   is_prime_rel n.

(* 辅助：按空格分词（携带当前累计的单词 cur，并在 words_rev 中按出现顺序的反向收集） *)
Inductive split_words_aux_rel : list ascii -> list ascii -> list (list ascii) -> Prop :=
| swar_nil_empty : split_words_aux_rel nil nil nil
| swar_nil_word : forall cur, cur <> nil -> split_words_aux_rel nil cur ((rev cur) :: nil)
| swar_space_skip : forall cs words_rev,
    split_words_aux_rel cs nil words_rev ->
    split_words_aux_rel (" "%char :: cs) nil words_rev
| swar_space_finish : forall cs cur words_rev,
    cur <> nil ->
    split_words_aux_rel cs nil words_rev ->
    split_words_aux_rel (" "%char :: cs) cur ((rev cur) :: words_rev)
| swar_char : forall c cs cur words_rev,
    Ascii.eqb c " "%char = false ->
    split_words_aux_rel cs (c :: cur) words_rev ->
    split_words_aux_rel (c :: cs) cur words_rev.

(* 对外关系：将反向收集的 words_rev 反转成正向顺序 *)
Inductive split_words_rel : list ascii -> list (list ascii) -> Prop :=
| swr_build : forall s words_rev words,
    split_words_aux_rel s nil words_rev ->
    words = rev words_rev ->
    split_words_rel s words.

Inductive filter_prime_length_rel : list (list ascii) -> list (list ascii) -> Prop :=
| fplr_nil : filter_prime_length_rel nil nil
| fplr_keep : forall w ws res, is_prime_rel (length w) -> filter_prime_length_rel ws res ->
    filter_prime_length_rel (w :: ws) (w :: res)
| fplr_drop : forall w ws res, ~ is_prime_rel (length w) -> filter_prime_length_rel ws res ->
    filter_prime_length_rel (w :: ws) res.

Inductive join_words_rel : list (list ascii) -> list ascii -> Prop :=
| jwr_nil : join_words_rel nil nil
| jwr_single : forall w, join_words_rel (w :: nil) w
| jwr_multi : forall w ws res, join_words_rel ws res ->
    join_words_rel (w :: ws) (w ++ (" "%char :: nil) ++ res).

(* 约束：1 <= 长度 <= 100；内容为英文字母或空格 *)
Definition problem_143_pre (sentence : string) : Prop :=
  let l := list_ascii_of_string sentence in
  1 <= length l /\ length l <= 100 /\
  Forall (fun c =>
    let n := nat_of_ascii c in c = " "%char \/ (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_143_spec (sentence : string) (output : string) : Prop :=
  exists words filtered, split_words_rel (list_ascii_of_string sentence) words /\
    filter_prime_length_rel words filtered /\
    join_words_rel filtered (list_ascii_of_string output).

Lemma is_prime_rel_2 : is_prime_rel 2.
Proof.
  apply ipr_prime.
  - lia.
  - intros [d [[Hd_ge Hd_le] HdDiv]].
    lia.
Qed.

Lemma not_is_prime_rel_1 : ~ is_prime_rel 1.
Proof.
  intros H.
  inversion H as [n Hgt Hno]; lia.
Qed.

Lemma not_is_prime_rel_4 : ~ is_prime_rel 4.
Proof.
  intros H.
  inversion H as [n Hgt Hno]; subst.
  assert (Hex : exists d, 2 <= d <= 3 /\ has_divisor_from_rel 4 d).
  { exists 2. split.
    - split; lia.
    - apply hdfr_base.
      + vm_compute. reflexivity.
      + lia.
  }
  apply Hno in Hex. contradiction.
Qed.

Example test_problem_143_example :
  problem_143_spec ("This is a test"%string) ("is"%string).
Proof.
  unfold problem_143_spec.
  (* Define words and filtered explicitly as lists of ascii, not strings *)
  set (wThis := ("T"%char :: "h"%char :: "i"%char :: "s"%char :: nil)).
  set (wis := ("i"%char :: "s"%char :: nil)).
  set (wa := ("a"%char :: nil)).
  set (wtest := ("t"%char :: "e"%char :: "s"%char :: "t"%char :: nil)).
  set (words_rev := (wThis :: wis :: wa :: wtest :: nil)).
  set (words := (wtest :: wa :: wis :: wThis :: nil)).
  set (filtered := (wis :: nil)).
  exists words, filtered.
  split.
  - (* split_words_rel *)
    apply swr_build with (words_rev := words_rev).
    + (* split_words_aux_rel over the input sentence *)
      (* "This is a test" *)
      eapply swar_char. vm_compute. reflexivity.
      eapply swar_char. vm_compute. reflexivity.
      eapply swar_char. vm_compute. reflexivity.
      eapply swar_char. vm_compute. reflexivity.
      eapply swar_space_finish.
      * discriminate.
      * (* "is a test" *)
        eapply swar_char. vm_compute. reflexivity.
        eapply swar_char. vm_compute. reflexivity.
        eapply swar_space_finish.
        -- discriminate.
        -- (* "a test" *)
           eapply swar_char. vm_compute. reflexivity.
           eapply swar_space_finish.
           ++ discriminate.
           ++ (* "test" *)
              eapply swar_char. vm_compute. reflexivity.
              eapply swar_char. vm_compute. reflexivity.
              eapply swar_char. vm_compute. reflexivity.
              eapply swar_char. vm_compute. reflexivity.
              apply swar_nil_word. discriminate.
    + simpl. reflexivity.
  - split.
    + (* filter_prime_length_rel words filtered *)
      (* words = [wtest; wa; wis; wThis] -> filtered = [wis] *)
      apply fplr_drop.
      * (* ~ prime length 4 *)
        simpl. apply not_is_prime_rel_4.
      * apply fplr_drop.
        -- (* ~ prime length 1 *)
           simpl. apply not_is_prime_rel_1.
        -- apply fplr_keep.
           ++ (* prime length 2 *)
              simpl. apply is_prime_rel_2.
           ++ apply fplr_drop.
              ** (* ~ prime length 4 *)
                 simpl. apply not_is_prime_rel_4.
              ** apply fplr_nil.
    + (* join_words_rel filtered (list_ascii_of_string "is") *)
      simpl. apply jwr_single.
Qed.