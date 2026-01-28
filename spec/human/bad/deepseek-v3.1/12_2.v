Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition problem_12_pre (input : list string) : Prop := True.

Definition problem_12_spec (input : list string) (output : option string) : Prop :=
  (input = [] /\ output = None) \/
  (exists out i,
    output = Some out /\
    List.length input > 0 /\
    i < List.length input /\
    nth_error input i = Some out /\
    (forall j, j < List.length input -> exists s, nth_error input j = Some s -> String.length s <= String.length out) /\
    (forall j, j < i -> exists s, nth_error input j = Some s -> String.length s < String.length out)
  ).

Example test_single_list : problem_12_spec ["x"; "y"; "z"] (Some "x").
Proof.
  unfold problem_12_spec.
  right.
  exists "x".
  exists 0.
  split.
  - reflexivity.
  - split.
    + lia.
    + split.
      * lia.
      * split.
        -- reflexivity.
        * split.
          -- intros j Hj.
             exists ("x"; "y"; "z").
             rewrite nth_error_cons.
             destruct (Nat.eq_dec j 0); subst; simpl; auto.
             -- lia.
          -- intros j Hj.
             exists ("x"; "y"; "z").
             rewrite nth_error_cons.
             destruct (Nat.eq_dec j 0); subst; simpl; auto.
             -- lia.
Qed.