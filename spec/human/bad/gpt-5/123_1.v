Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint collatz_aux (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if Z.eqb n 1 then [1]
    else
      let next := if Z.even n then n / 2 else 3 * n + 1 in
      n :: collatz_aux next fuel'
  end.

Definition collatz_list (n : Z) (l : list Z) : Prop :=
  exists fuel, collatz_aux n fuel = l /\ last l 0 = 1.

Definition problem_123_pre (n : Z) : Prop := n > 0.

Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists (c_seq : list Z),
    collatz_list n c_seq /\
    Permutation result (filter (fun x => Z.odd x) c_seq) /\
    Sorted Z.le result.

Example test_problem_123_14 :
  problem_123_spec 14%Z [1%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z].
Proof.
  unfold problem_123_spec.
  exists [14%Z; 7%Z; 22%Z; 11%Z; 34%Z; 17%Z; 52%Z; 26%Z; 13%Z; 40%Z; 20%Z; 10%Z; 5%Z; 16%Z; 8%Z; 4%Z; 2%Z; 1%Z].
  split.
  - unfold collatz_list.
    exists 18%nat.
    split.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
  - split.
    + vm_compute.
      (* We need to show: Permutation [1;5;7;11;13;17] [7;11;17;13;5;1]. *)
      eapply Permutation_trans with ([5%Z; 1%Z; 7%Z; 11%Z; 13%Z; 17%Z]).
      * (* swap 1 and 5 at head *)
        apply perm_swap.
      * eapply Permutation_trans with ([5%Z; 1%Z] ++ [7%Z; 11%Z; 17%Z; 13%Z]).
        -- (* swap the last two elements 13 and 17 in tail *)
           apply perm_skip.
           apply perm_skip.
           apply perm_skip.
           apply perm_skip.
           apply perm_swap.
        -- (* commute the two appended lists *)
           simpl.
           apply Permutation_app_comm.
    + (* Sorted Z.le [1; 5; 7; 11; 13; 17] *)
      constructor.
      * intros y Hy. simpl in Hy.
        destruct Hy as [Hy|Hy]; subst; try lia.
        destruct Hy as [Hy|Hy]; subst; try lia.
        destruct Hy as [Hy|Hy]; subst; try lia.
        destruct Hy as [Hy|Hy]; subst; try lia.
        destruct Hy as [Hy|Hy]; subst; try lia.
        contradiction.
      * constructor.
        -- intros y Hy. simpl in Hy.
           destruct Hy as [Hy|Hy]; subst; try lia.
           destruct Hy as [Hy|Hy]; subst; try lia.
           destruct Hy as [Hy|Hy]; subst; try lia.
           destruct Hy as [Hy|Hy]; subst; try lia.
           contradiction.
        -- constructor.
           ++ intros y Hy. simpl in Hy.
              destruct Hy as [Hy|Hy]; subst; try lia.
              destruct Hy as [Hy|Hy]; subst; try lia.
              destruct Hy as [Hy|Hy]; subst; try lia.
              contradiction.
           ++ constructor.
              ** intros y Hy. simpl in Hy.
                 destruct Hy as [Hy|Hy]; subst; try lia.
                 destruct Hy as [Hy|Hy]; subst; try lia.
                 contradiction.
              ** constructor.
                 --- intros y Hy. simpl in Hy.
                     destruct Hy as [Hy|Hy]; subst; try lia.
                     contradiction.
                 --- constructor.
                     +++ intros y Hy. simpl in Hy. contradiction.
                     +++ constructor.
Qed.