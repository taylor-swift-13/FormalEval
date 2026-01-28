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

(* Test case: input = "mississippi", substring = "ss", output = 2 *)
Example test_problem_18_mississippi : problem_18_spec "mississippi" "ss" 2.
Proof.
  unfold problem_18_spec.
  exists [2; 5].
  split.
  - apply NoDup_cons.
    + intro H. simpl in H. destruct H; lia.
    + apply NoDup_cons.
      * intro H. simpl in H. destruct H; lia.
      * apply NoDup_nil.
  - split.
    + intros i H_in.
      simpl in H_in.
      destruct H_in as [H2 | [H5 | H_false]].
      * subst. unfold match_at. simpl.
        split; [lia | ]. split; [lia | ].
        intros j Hj.
        destruct j as [|j]; [reflexivity | ].
        destruct j as [|j]; [reflexivity | ].
        lia.
      * subst. unfold match_at. simpl.
        split; [lia | ]. split; [lia | ].
        intros j Hj.
        destruct j as [|j]; [reflexivity | ].
        destruct j as [|j]; [reflexivity | ].
        lia.
      * contradiction.
    + split.
      * intros i H_bound H_match.
        unfold match_at in H_match.
        destruct H_match as [_ [_ H_eq]].
        simpl in H_bound.
        destruct i. { specialize (H_eq 0). simpl in H_eq. assert (0 < 2) by lia. specialize (H_eq H). discriminate. }
        destruct i. { specialize (H_eq 0). simpl in H_eq. assert (0 < 2) by lia. specialize (H_eq H). discriminate. }
        destruct i. { left. reflexivity. }
        destruct i. { specialize (H_eq 1). simpl in H_eq. assert (1 < 2) by lia. specialize (H_eq H). discriminate. }
        destruct i. { specialize (H_eq 0). simpl in H_eq. assert (0 < 2) by lia. specialize (H_eq H). discriminate. }
        destruct i. { right. left. reflexivity. }
        destruct i. { specialize (H_eq 1). simpl in H_eq. assert (1 < 2) by lia. specialize (H_eq H). discriminate. }
        destruct i. { specialize (H_eq 0). simpl in H_eq. assert (0 < 2) by lia. specialize (H_eq H). discriminate. }
        destruct i. { specialize (H_eq 0). simpl in H_eq. assert (0 < 2) by lia. specialize (H_eq H). discriminate. }
        destruct i. { specialize (H_eq 0). simpl in H_eq. assert (0 < 2) by lia. specialize (H_eq H). discriminate. }
        lia.
      * simpl. reflexivity.
Qed.