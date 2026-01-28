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

(* Test case: input = "aaacarabbbbcccc", substring = "efg", output = 0 *)
Example test_problem_18_no_match : problem_18_spec "aaacarabbbbcccc" "efg" 0.
Proof.
  unfold problem_18_spec.
  exists [].
  split.
  - apply NoDup_nil.
  - split.
    + intros i H. inversion H.
    + split.
      * intros i H_bound H_match.
        unfold match_at in H_match.
        destruct H_match as [_ [_ H_eq]].
        (* Check first char equality: input[i] == 'e' *)
        specialize (H_eq 0).
        assert (H_lt : 0 < 3) by lia.
        specialize (H_eq H_lt).
        replace (i + 0) with i in H_eq by lia.
        simpl in H_eq.
        (* Iterate through indices. Length of input is 15. *)
        do 16 (destruct i; [ simpl in H_eq; try discriminate | ]).
        (* For remaining i, the bound condition fails *)
        simpl in H_bound. lia.
      * simpl. reflexivity.
Qed.