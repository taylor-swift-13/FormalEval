Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Lia.

Import ListNotations.

Open Scope string_scope.

Fixpoint count (x : string) (l : list string) : nat :=
  match l with
  | [] => 0
  | y :: ys => if string_dec x y then S (count x ys) else count x ys
  end.

Definition ascii_lt (a b : ascii) : Prop :=
  nat_of_ascii a < nat_of_ascii b.

Fixpoint string_lex_lt (s t : string) : Prop :=
  match s, t with
  | EmptyString, EmptyString => False
  | EmptyString, String _ _ => True
  | String _ _, EmptyString => False
  | String a s', String b t' =>
      ascii_lt a b \/ (a = b /\ string_lex_lt s' t')
  end.

Definition string_lex_le (s t : string) : Prop :=
  s = t \/ string_lex_lt s t.

Definition even_length (s : string) : Prop :=
  exists k : nat, String.length s = 2 * k.

Definition orderR (s t : string) : Prop :=
  String.length s < String.length t \/
  (String.length s = String.length t /\ string_lex_le s t).

Definition sorted_list_sum_spec (lst res : list string) : Prop :=
  (forall s : string, even_length s -> count s res = count s lst) /\
  (forall s : string, ~ even_length s -> count s res = 0) /\
  Sorted orderR res.

Lemma odd_length_a : ~ even_length "a".
Proof.
  unfold even_length, not.
  intros [k Hk].
  simpl in Hk.
  lia.
Qed.

Lemma odd_length_aaa : ~ even_length "aaa".
Proof.
  unfold even_length, not.
  intros [k Hk].
  simpl in Hk.
  lia.
Qed.

Lemma even_length_aa : even_length "aa".
Proof.
  unfold even_length.
  exists 1.
  simpl.
  reflexivity.
Qed.

Example test_sorted_list_sum :
  sorted_list_sum_spec ("aa" :: "a" :: "aaa" :: nil) ("aa" :: nil).
Proof.
  unfold sorted_list_sum_spec.
  repeat split.
  - (* even_length strings have same count *)
    intros s Heven.
    simpl.
    destruct (string_dec s "aa") as [Heq | Hneq].
    + (* s = "aa" *)
      subst s.
      destruct (string_dec "aa" "a") as [H1|H1]; try discriminate.
      destruct (string_dec "aa" "aaa") as [H2|H2]; try discriminate.
      reflexivity.
    + (* s <> "aa" *)
      destruct (string_dec s "a") as [Heq_a | Hneq_a].
      * (* s = "a" - but "a" has odd length, contradiction *)
        subst s.
        exfalso.
        apply odd_length_a.
        exact Heven.
      * destruct (string_dec s "aaa") as [Heq_aaa | Hneq_aaa].
        -- (* s = "aaa" - but "aaa" has odd length, contradiction *)
           subst s.
           exfalso.
           apply odd_length_aaa.
           exact Heven.
        -- (* s is none of the input strings *)
           reflexivity.
  - (* odd_length strings have count 0 *)
    intros s Hodd.
    simpl.
    destruct (string_dec s "aa") as [Heq | Hneq].
    + (* s = "aa" - but "aa" has even length, contradiction *)
      subst s.
      exfalso.
      apply Hodd.
      exact even_length_aa.
    + reflexivity.
  - (* result is sorted - single element list *)
    apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
Qed.