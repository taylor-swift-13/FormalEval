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

(* Test case: input = "bbb", substring = "bb", output = 2 *)
Example test_problem_18_bbb_bb : problem_18_spec "bbb" "bb" 2.
Proof.
  unfold problem_18_spec.
  exists [0; 1].
  split.
  - (* NoDup [0; 1] *)
    repeat constructor; simpl; try lia.
  - split.
    + (* forall i, In i [0; 1] -> match_at ... *)
      intros i H_in.
      destruct H_in as [H0 | [H1 | H_nil]].
      * (* i = 0 *)
        subst.
        unfold match_at.
        simpl.
        split; [lia |].
        split; [lia |].
        intros j H_j.
        destruct j as [|j].
        { reflexivity. }
        destruct j as [|j].
        { reflexivity. }
        lia.
      * (* i = 1 *)
        subst.
        unfold match_at.
        simpl.
        split; [lia |].
        split; [lia |].
        intros j H_j.
        destruct j as [|j].
        { reflexivity. }
        destruct j as [|j].
        { reflexivity. }
        lia.
      * contradiction.
    + split.
      * (* forall i, ... -> In i [0; 1] *)
        intros i H_bound H_match.
        simpl in H_bound.
        assert (i = 0 \/ i = 1) as H_idx by lia.
        destruct H_idx as [H0 | H1]; subst.
        -- left; reflexivity.
        -- right; left; reflexivity.
      * (* output = length [0; 1] *)
        simpl.
        reflexivity.
Qed.