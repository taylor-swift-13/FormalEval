Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.

Fixpoint string_le (s1 s2 : string) : Prop :=
  match s1, s2 with
  | EmptyString, _ => True
  | String _ _, EmptyString => False
  | String c1 s1', String c2 s2' =>
      (nat_of_ascii c1 < nat_of_ascii c2) \/ (nat_of_ascii c1 = nat_of_ascii c2 /\ string_le s1' s2')
  end.

Definition problem_34_pre (input : list string) : Prop := True.

Definition problem_34_spec (input : list string) (output : list string) : Prop :=
  Sorted string_le output /\
  NoDup output /\
  (forall s, In s input <-> In s output).

Example test_problem_34 :
  problem_34_spec ["apple"; "banana"; "lQd"; "oralQdnge"] ["apple"; "banana"; "lQd"; "oralQdnge"].
Proof.
  unfold problem_34_spec.
  split.
  { 
    repeat constructor.
    all: simpl; intuition; try lia.
  }
  split.
  { 
    repeat constructor.
    all: simpl; intuition; try discriminate.
  }
  { 
    intro z.
    split; intro H; simpl in *; intuition; subst; auto.
  }
Qed.