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

Example test_problem_18_ababa : problem_18_spec "ababa" "ababa" 1.
Proof.
  unfold problem_18_spec.
  exists [0].
  split.
  - apply NoDup_cons.
    + intro H. inversion H.
    + apply NoDup_nil.
  - split.
    + intros i H_in.
      destruct H_in as [H_eq | H_false].
      * rewrite <- H_eq.
        unfold match_at.
        simpl.
        split.
        -- lia.
        -- split.
           ++ lia.
           ++ intros j H_len.
              reflexivity.
      * inversion H_false.
    + split.
      * intros i H_bound H_match.
        simpl in H_bound.
        assert (i = 0) by lia.
        subst.
        left. reflexivity.
      * simpl. reflexivity.
Qed.