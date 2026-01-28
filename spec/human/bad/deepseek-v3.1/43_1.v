Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_43_spec (input : list Z) (output : bool) : Prop :=
  (exists i j : nat,
    (i <> j) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (nth i input 0 + nth j input 0 = 0))
  <-> (output = true).

Example test_case_1 : problem_43_spec [1; 3; 5; 0] false.
Proof.
  unfold problem_43_spec.
  split.
  - intros H.
    destruct H as (i & j & Hneq & Hlen_i & Hlen_j & Hsum).
    exfalso.
    (* Compute all possible pairs and verify none sum to 0 *)
    simpl in Hlen_i, Hlen_j.
    (* Since the list has length 4, i,j can only be 0,1,2,3 *)
    assert (i < 4)%nat as Hi_bound by apply Hlen_i.
    assert (j < 4)%nat as Hj_bound by apply Hlen_j.
    (* Check all 12 possible distinct pairs *)
    destruct i as [| [| [| [| i]]]];
      destruct j as [| [| [| [| j]]]];
      try (apply Hneq; reflexivity);
      simpl in Hsum;
      compute in Hsum;
      discriminate Hsum.
  - intros H.
    discriminate H.
Qed.