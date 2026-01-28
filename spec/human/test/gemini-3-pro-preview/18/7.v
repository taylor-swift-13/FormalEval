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

Example test_problem_18_overlap : problem_18_spec "abababab" "aba" 3.
Proof.
  unfold problem_18_spec.
  exists [0; 2; 4].
  split.
  - (* NoDup *)
    apply NoDup_cons.
    + simpl; lia.
    + apply NoDup_cons.
      * simpl; lia.
      * apply NoDup_cons.
        -- simpl; lia.
        -- apply NoDup_nil.
  - split.
    + (* Valid matches *)
      intros i H_in.
      simpl in H_in.
      destruct H_in as [H0 | [H2 | [H4 | H_false]]].
      * (* i = 0 *)
        subst. unfold match_at. split. simpl; lia. split. simpl; lia.
        intros j Hj. simpl in Hj.
        repeat (destruct j; [ reflexivity | ]).
        simpl in Hj; lia.
      * (* i = 2 *)
        subst. unfold match_at. split. simpl; lia. split. simpl; lia.
        intros j Hj. simpl in Hj.
        repeat (destruct j; [ reflexivity | ]).
        simpl in Hj; lia.
      * (* i = 4 *)
        subst. unfold match_at. split. simpl; lia. split. simpl; lia.
        intros j Hj. simpl in Hj.
        repeat (destruct j; [ reflexivity | ]).
        simpl in Hj; lia.
      * contradiction.
    + split.
      * (* Completeness *)
        intros i H_bound H_match.
        simpl in H_bound.
        unfold match_at in H_match. destruct H_match as [_ [_ H_chars]].
        assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as H_cases by lia.
        destruct H_cases as [C0 | [C1 | [C2 | [C3 | [C4 | C5]]]]].
        -- subst. simpl. left. reflexivity.
        -- subst.
           specialize (H_chars 0).
           simpl in H_chars.
           assert (0 < 3) by lia.
           specialize (H_chars H).
           simpl in H_chars. discriminate.
        -- subst. simpl. right. left. reflexivity.
        -- subst.
           specialize (H_chars 0).
           simpl in H_chars.
           assert (0 < 3) by lia.
           specialize (H_chars H).
           simpl in H_chars. discriminate.
        -- subst. simpl. right. right. left. reflexivity.
        -- subst.
           specialize (H_chars 0).
           simpl in H_chars.
           assert (0 < 3) by lia.
           specialize (H_chars H).
           simpl in H_chars. discriminate.
      * (* Count *)
        reflexivity.
Qed.