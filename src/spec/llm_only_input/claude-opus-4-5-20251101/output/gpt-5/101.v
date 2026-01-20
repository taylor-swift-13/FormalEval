Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Open Scope string_scope.

Definition char_string (c : Ascii.ascii) : string := String c EmptyString.

Definition sep_char (c : Ascii.ascii) : Prop :=
  char_string c = " " \/ char_string c = ",".

Definition not_sep_char (c : Ascii.ascii) : Prop := ~ sep_char c.

Fixpoint all_chars (P : Ascii.ascii -> Prop) (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c s' => P c /\ all_chars P s'
  end.

Definition only_seps (s : string) : Prop := all_chars sep_char s.

Definition word (s : string) : Prop := s <> EmptyString /\ all_chars not_sep_char s.

Inductive components : list string -> list string -> Prop :=
| components_end : forall sep, only_seps sep -> components (sep :: nil) nil
| components_cons : forall sep w rest words,
    only_seps sep -> word w -> components rest words ->
    components (sep :: w :: rest) (w :: words).

Fixpoint concat (xs : list string) : string :=
  match xs with
  | nil => EmptyString
  | x :: xs' => x ++ concat xs'
  end.

Definition words_string_spec (s : string) (out : list string) : Prop :=
  exists comps words,
    components comps words /\ out = words /\ s = concat comps.

(* Helper lemmas for character properties *)
Lemma space_is_sep : sep_char " "%char.
Proof.
  unfold sep_char, char_string. left. reflexivity.
Qed.

Lemma comma_is_sep : sep_char ","%char.
Proof.
  unfold sep_char, char_string. right. reflexivity.
Qed.

Lemma H_not_sep : not_sep_char "H"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma i_not_sep : not_sep_char "i"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma m_not_sep : not_sep_char "m"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma y_not_sep : not_sep_char "y"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma n_not_sep : not_sep_char "n"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma a_not_sep : not_sep_char "a"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma e_not_sep : not_sep_char "e"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma s_not_sep : not_sep_char "s"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma J_not_sep : not_sep_char "J"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma o_not_sep : not_sep_char "o"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Lemma h_not_sep : not_sep_char "h"%char.
Proof.
  unfold not_sep_char, sep_char, char_string.
  intros [H | H]; discriminate.
Qed.

Example test_words_string :
  words_string_spec "Hi, my name is John" ("Hi" :: "my" :: "name" :: "is" :: "John" :: nil).
Proof.
  unfold words_string_spec.
  exists ("" :: "Hi" :: ", " :: "my" :: " " :: "name" :: " " :: "is" :: " " :: "John" :: "" :: nil).
  exists ("Hi" :: "my" :: "name" :: "is" :: "John" :: nil).
  split.
  - (* components proof *)
    apply components_cons.
    + unfold only_seps, all_chars. exact I.
    + unfold word. split.
      * discriminate.
      * unfold all_chars. split. apply H_not_sep. split. apply i_not_sep. exact I.
    + apply components_cons.
      * unfold only_seps, all_chars. split. apply comma_is_sep. split. apply space_is_sep. exact I.
      * unfold word. split.
        -- discriminate.
        -- unfold all_chars. split. apply m_not_sep. split. apply y_not_sep. exact I.
      * apply components_cons.
        -- unfold only_seps, all_chars. split. apply space_is_sep. exact I.
        -- unfold word. split.
           ++ discriminate.
           ++ unfold all_chars. split. apply n_not_sep. split. apply a_not_sep. 
              split. apply m_not_sep. split. apply e_not_sep. exact I.
        -- apply components_cons.
           ++ unfold only_seps, all_chars. split. apply space_is_sep. exact I.
           ++ unfold word. split.
              ** discriminate.
              ** unfold all_chars. split. apply i_not_sep. split. apply s_not_sep. exact I.
           ++ apply components_cons.
              ** unfold only_seps, all_chars. split. apply space_is_sep. exact I.
              ** unfold word. split.
                 --- discriminate.
                 --- unfold all_chars. split. apply J_not_sep. split. apply o_not_sep.
                     split. apply h_not_sep. split. apply n_not_sep. exact I.
              ** apply components_end. unfold only_seps, all_chars. exact I.
  - split.
    + reflexivity.
    + simpl. reflexivity.
Qed.