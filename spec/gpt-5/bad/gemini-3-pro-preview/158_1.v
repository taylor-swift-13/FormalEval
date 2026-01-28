Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Sorting.Permutation.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* Specification Definitions *)

Fixpoint chars_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String a s' => a :: chars_of_string s'
  end.

Definition unique_char_count (s : string) (n : nat) : Prop :=
  exists l : list ascii,
    NoDup l /\
    (forall a : ascii, In a l <-> In a (chars_of_string s)) /\
    length l = n.

Definition find_max_spec (words : list string) (ans : string) : Prop :=
  match words with
  | nil => ans = EmptyString
  | _ =>
    In ans words /\
    exists n : nat,
      unique_char_count ans n /\
      (forall w n', In w words -> unique_char_count w n' -> n' <= n) /\
      (forall w, In w words -> unique_char_count w n -> ~ String_as_OT.lt w ans)
  end.

(* Helper Lemma: If the string chars are already NoDup, n is just the length *)
Lemma unique_count_det : forall s n,
  unique_char_count s n ->
  NoDup (chars_of_string s) ->
  n = length (chars_of_string s).
Proof.
  intros s n Huniq Hnd_s.
  destruct Huniq as [l [Hnd_l [Hiff Hlen]]].
  assert (Hperm : Permutation l (chars_of_string s)).
  { apply NoDup_Permutation; auto. intro a. apply Hiff. }
  apply Permutation_length in Hperm.
  rewrite Hlen in Hperm.
  symmetry. apply Hperm.
Qed.

(* Test Case Proof *)
Example test_case : find_max_spec ["name"; "of"; "string"] "string".
Proof.
  (* Unfold the function logic for the specific list *)
  simpl.
  split.
  - (* Prove "string" is in the list *)
    repeat (constructor || auto).
  - (* Prove the existence of n=6 and its properties *)
    exists 6.
    split.
    + (* Prove unique_char_count "string" 6 *)
      exists (chars_of_string "string").
      split.
      * (* NoDup *)
        simpl. repeat constructor; try discriminate.
      * (* Equivalence and Length *)
        split; reflexivity.
    + split.
      * (* Prove 6 is the max length among words *)
        intros w n' Hin Huniq.
        destruct Hin as [H | [H | [H | H]]]; subst w.
        -- (* "name" has length 4 *)
           assert (Hnd: NoDup (chars_of_string "name")) by (simpl; repeat constructor; discriminate).
           apply unique_count_det in Huniq; auto.
           simpl in Huniq. rewrite Huniq. lia.
        -- (* "of" has length 2 *)
           assert (Hnd: NoDup (chars_of_string "of")) by (simpl; repeat constructor; discriminate).
           apply unique_count_det in Huniq; auto.
           simpl in Huniq. rewrite Huniq. lia.
        -- (* "string" has length 6 *)
           assert (Hnd: NoDup (chars_of_string "string")) by (simpl; repeat constructor; discriminate).
           apply unique_count_det in Huniq; auto.
           simpl in Huniq. rewrite Huniq. lia.
        -- (* Contradiction for empty tail *)
           contradiction.
      * (* Prove tie-breaking condition *)
        intros w Hin Huniq Hlt.
        destruct Hin as [H | [H | [H | H]]]; subst w.
        -- (* "name": count 4 != 6 *)
           assert (Hnd: NoDup (chars_of_string "name")) by (simpl; repeat constructor; discriminate).
           apply unique_count_det in Huniq; auto.
           simpl in Huniq. discriminate.
        -- (* "of": count 2 != 6 *)
           assert (Hnd: NoDup (chars_of_string "of")) by (simpl; repeat constructor; discriminate).
           apply unique_count_det in Huniq; auto.
           simpl in Huniq. discriminate.
        -- (* "string": not lt "string" "string" *)
           apply String_as_OT.lt_not_eq in Hlt.
           contradiction Hlt. reflexivity.
        -- contradiction.
Qed.