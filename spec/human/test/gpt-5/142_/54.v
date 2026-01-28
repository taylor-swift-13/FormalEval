Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_transformed_rel : list Z -> nat -> Z -> Prop :=
| str_nil : forall i, sum_transformed_rel [] i 0%Z
| str_cons : forall h t i s_tail term,
   ((Nat.eqb (i mod 3) 0 = true -> term = h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = true -> term = h * h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = false -> term = h)) ->
   sum_transformed_rel t (S i) s_tail ->
   sum_transformed_rel (h :: t) i (term + s_tail).

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (res : Z) : Prop :=
  sum_transformed_rel lst 0%nat res.

Example test_case_sum_squares :
  problem_142_spec [6%Z; 9%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 12%Z] 8466%Z.
Proof.
  unfold problem_142_spec.
  replace 8466%Z with (36%Z + 8430%Z) by lia.
  apply (str_cons 6%Z [9%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 12%Z] 0%nat 8430%Z 36%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  replace 8430%Z with (9%Z + 8421%Z) by lia.
  apply (str_cons 9%Z [12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 12%Z] 1%nat 8421%Z 9%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; vm_compute; reflexivity ] ].
  replace 8421%Z with (12%Z + 8409%Z) by lia.
  apply (str_cons 12%Z [15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 12%Z] 2%nat 8409%Z 12%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; vm_compute; reflexivity ] ].
  replace 8409%Z with (225%Z + 8184%Z) by lia.
  apply (str_cons 15%Z [18%Z; 21%Z; 24%Z; 27%Z; 12%Z] 3%nat 8184%Z 225%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 8184%Z with (5832%Z + 2352%Z) by lia.
  apply (str_cons 18%Z [21%Z; 24%Z; 27%Z; 12%Z] 4%nat 2352%Z 5832%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 2352%Z with (21%Z + 2331%Z) by lia.
  apply (str_cons 21%Z [24%Z; 27%Z; 12%Z] 5%nat 2331%Z 21%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; vm_compute; reflexivity ] ].
  replace 2331%Z with (576%Z + 1755%Z) by lia.
  apply (str_cons 24%Z [27%Z; 12%Z] 6%nat 1755%Z 576%Z).
  split; [ intros _; vm_compute; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  replace 1755%Z with (27%Z + 1728%Z) by lia.
  apply (str_cons 27%Z [12%Z] 7%nat 1728%Z 27%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; vm_compute; reflexivity ] ].
  replace 1728%Z with (1728%Z + 0%Z) by lia.
  apply (str_cons 12%Z [] 8%nat 0%Z 1728%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; vm_compute; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_nil 9%nat).
Qed.