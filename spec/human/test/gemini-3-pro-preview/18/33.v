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

(* Test case: input = "thebquickbrownfox", substring = "thequickbrownfox", output = 0 *)
Example test_problem_18_new : problem_18_spec "thebquickbrownfox" "thequickbrownfox" 0.
Proof.
  unfold problem_18_spec.
  exists [].
  split.
  - apply NoDup_nil.
  - split.
    + intros i H_in. inversion H_in.
    + split.
      * intros i H_bound H_match.
        unfold match_at in H_match.
        destruct H_match as [_ [_ H_eq]].
        simpl in H_bound.
        assert (i = 0 \/ i = 1) as H_i by lia.
        destruct H_i as [H0 | H1].
        -- subst i.
           specialize (H_eq 3).
           assert (3 < 16) as H_j by lia.
           specialize (H_eq H_j).
           simpl in H_eq.
           inversion H_eq.
        -- subst i.
           specialize (H_eq 0).
           assert (0 < 16) as H_j by lia.
           specialize (H_eq H_j).
           simpl in H_eq.
           inversion H_eq.
      * simpl. reflexivity.
Qed.