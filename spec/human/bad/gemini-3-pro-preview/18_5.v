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

(* Test case: input = "ababa", substring = "aba", output = 2 *)
Example test_problem_18_ababa : problem_18_spec "ababa" "aba" 2.
Proof.
  unfold problem_18_spec.
  (* The matches are at indices 0 and 2 *)
  exists [0; 2].
  split.
  - (* NoDup [0; 2] *)
    repeat constructor; simpl; try intro H; try destruct H; try discriminate.
  - split.
    + (* forall i, In i [0; 2] -> match_at i "ababa" "aba" *)
      intros i H_in.
      simpl in H_in.
      destruct H_in as [H0 | [H2 | H_false]].
      * (* i = 0 *)
        subst.
        unfold match_at.
        simpl.
        split; [lia | split; [lia | ]].
        intros j Hj.
        (* Check characters for j=0,1,2 *)
        do 3 (destruct j; [simpl; reflexivity | ]).
        lia.
      * (* i = 2 *)
        subst.
        unfold match_at.
        simpl.
        split; [lia | split; [lia | ]].
        intros j Hj.
        (* Check characters for j=0,1,2 *)
        do 3 (destruct j; [simpl; reflexivity | ]).
        lia.
      * contradiction.
    + split.
      * (* forall i, ... -> In i [0; 2] *)
        intros i H_bound H_match.
        unfold match_at in H_match.
        destruct H_match as [_ [_ H_forall]].
        simpl in H_bound.
        (* i + 3 <= 5 implies i <= 2 *)
        assert (i < 3) as Hi by lia.
        destruct i.
        -- (* i = 0 *)
           left. reflexivity.
        -- destruct i.
           ++ (* i = 1 *)
              exfalso.
              (* Check mismatch at j=0: input[1] = 'b', substr[0] = 'a' *)
              specialize (H_forall 0).
              simpl in H_forall.
              assert (0 < 3) as H_0_lt_3 by lia.
              specialize (H_forall H_0_lt_3).
              simpl in H_forall.
              discriminate H_forall.
           ++ destruct i.
              ** (* i = 2 *)
                 right. left. reflexivity.
              ** (* i >= 3 *)
                 lia.
      * (* output = length [0; 2] *)
        simpl.
        reflexivity.
Qed.