Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Require Import Lia.
Open Scope string_scope.

(* Definition of match_at as per specification *)
Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

(* Precondition (True as default) *)
Definition problem_18_pre (input substring : string) : Prop := True.

(* Specification definition *)
Definition problem_18_spec (input substring : string) (output : nat) : Prop :=
  exists indices : list nat,
    NoDup indices /\
    (* All indices in the list are valid matches *)
    (forall i, In i indices -> match_at i input substring) /\
    (* All valid matches are in the list *)
    (forall i, i + String.length substring <= String.length input ->
               match_at i input substring -> In i indices) /\
    (* Output is the count of matches *)
    output = List.length indices.

(* Test case: input = "john doe", substring = "john", output = 1 *)
Example test_problem_18_john_doe : problem_18_spec "john doe" "john" 1.
Proof.
  unfold problem_18_spec.
  exists [0].
  split.
  - apply NoDup_cons.
    + intros H. inversion H.
    + apply NoDup_nil.
  - split.
    + intros i H_in.
      destruct H_in as [H_eq | H_false].
      * subst. unfold match_at. split.
        -- simpl. lia.
        -- split.
           ++ simpl. lia.
           ++ intros j H_j. simpl in H_j.
              repeat (destruct j as [|j]; [reflexivity | ]).
              lia.
      * contradiction.
    + split.
      * intros i H_len H_match.
        unfold match_at in H_match. destruct H_match as [_ [_ H_chars]].
        (* Check indices i = 0, 1, 2, 3, 4 based on length constraint *)
        destruct i.
        -- (* i = 0 *)
           left. reflexivity.
        -- (* i = 1 *)
           destruct i.
           ++ specialize (H_chars 0). simpl in H_chars.
              assert (0 < 4) by lia. specialize (H_chars H).
              simpl in H_chars. discriminate.
           ++ (* i = 2 *)
              destruct i.
              ** specialize (H_chars 0). simpl in H_chars.
                 assert (0 < 4) by lia. specialize (H_chars H).
                 simpl in H_chars. discriminate.
              ** (* i = 3 *)
                 destruct i.
                 --- specialize (H_chars 0). simpl in H_chars.
                     assert (0 < 4) by lia. specialize (H_chars H).
                     simpl in H_chars. discriminate.
                 --- (* i = 4 *)
                     destruct i.
                     +++ specialize (H_chars 0). simpl in H_chars.
                         assert (0 < 4) by lia. specialize (H_chars H).
                         simpl in H_chars. discriminate.
                     +++ (* i >= 5 *)
                         simpl in H_len. lia.
      * simpl. reflexivity.
Qed.