Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint triples_sum_to_zero (input : list Z) : bool :=
  match input with
  | [] => false
  | x :: xs =>
      let fix find_pair (ys : list Z) :=
          match ys with
          | [] => false
          | y :: zs =>
              let fix find_third (zs' : list Z) :=
                  match zs' with
                  | [] => false
                  | z :: ws => (x + y + z =? 0) || find_third ws
                  end
              in find_third zs || find_pair zs
          end
      in find_pair xs || triples_sum_to_zero xs
  end.

Lemma problem_40_example1 : triples_sum_to_zero [1; 3; 5; 0] = false.
Proof.
  simpl.
  reflexivity.
Qed.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (exists i j k : nat,
    i <> j /\ i <> k /\ j <> k /\
    i < length input /\ j < length input /\ k < length input /\
    nth i input 0 + nth j input 0 + nth k input 0 = 0)
  <-> output = true.

Lemma example1_satisfies_spec : problem_40_spec [1; 3; 5; 0] false.
Proof.
  unfold problem_40_spec.
  split.
  - intros H.
    destruct H as (i & j & k & Hneq1 & Hneq2 & Hneq3 & Hlen1 & Hlen2 & Hlen3 & Hsum).
    simpl in Hlen1, Hlen2, Hlen3.
    repeat (match goal with
           | H : ?n < 4%nat |- _ => 
               assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3) by lia;
               destruct H as [Hn | [Hn | [Hn | Hn]]]; subst
           end).
    all: simpl in Hsum; lia.
  - intros H. discriminate H.
Qed.