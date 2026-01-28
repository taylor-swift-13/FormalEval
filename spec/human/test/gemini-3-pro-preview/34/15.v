Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.

Definition problem_34_pre (input : list string) : Prop := True.

Fixpoint string_le (s1 s2 : string) : Prop :=
  match s1, s2 with
  | EmptyString, _ => True
  | String _ _, EmptyString => False
  | String c1 s1', String c2 s2' =>
      let n1 := nat_of_ascii c1 in
      let n2 := nat_of_ascii c2 in
      (n1 < n2)%nat \/ ((n1 = n2)%nat /\ string_le s1' s2')
  end.

Definition problem_34_spec (input : list string) (output : list string) : Prop :=
  Sorted string_le output /\
  NoDup output /\
  (forall s, In s input <-> In s output).

Example test_problem_34 :
  problem_34_spec ["apple"; "banana"; "lQd"; "orange"] ["apple"; "banana"; "lQd"; "orange"].
Proof.
  unfold problem_34_spec.
  split.
  {
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons. compute. left. lia.
    - apply HdRel_cons. compute. left. lia.
    - apply HdRel_cons. compute. left. lia.
  }
  split.
  {
    repeat apply NoDup_cons.
    all: try (simpl; intuition; discriminate).
    apply NoDup_nil.
  }
  {
    intro z.
    split; auto.
  }
Qed.