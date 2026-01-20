Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.

Open Scope Z_scope.

Fixpoint count_ones_pos (p : positive) : nat :=
  match p with
  | xH => 1%nat
  | xO p' => count_ones_pos p'
  | xI p' => S (count_ones_pos p')
  end.

Definition count_ones (z : Z) : nat :=
  match z with
  | Z0 => 0%nat
  | Zpos p => count_ones_pos p
  | Zneg p => count_ones_pos p
  end.

Definition cmp (x y : Z) : comparison :=
  let x1 := count_ones x in
  let y1 := count_ones y in
  match Nat.compare x1 y1 with
  | Eq => Z.compare x y
  | Lt => Lt
  | Gt => Gt
  end.

Definition le_by_cmp (x y : Z) : Prop :=
  match cmp x y with
  | Lt => True
  | Eq => True
  | Gt => False
  end.

Definition lt_by_cmp (x y : Z) : Prop :=
  match cmp x y with
  | Lt => True
  | _ => False
  end.

Definition sort_array_spec (arr result : list Z) : Prop :=
  Permutation arr result /\
  (forall i j, (i < j)%nat -> 
    forall x y, nth_error result i = Some x -> 
                nth_error result j = Some y -> 
                le_by_cmp x y).

Example sort_array_example : sort_array_spec (0%Z :: 100000%Z :: 3%Z :: 7%Z :: 12%Z :: nil) (0%Z :: 3%Z :: 12%Z :: 7%Z :: 100000%Z :: nil).
Proof.
  unfold sort_array_spec.
  split.
  - (* Permutation proof *)
    apply perm_trans with (0%Z :: 3%Z :: 100000%Z :: 7%Z :: 12%Z :: nil).
    + apply perm_skip.
      apply perm_swap.
    + apply perm_trans with (0%Z :: 3%Z :: 7%Z :: 100000%Z :: 12%Z :: nil).
      * apply perm_skip. apply perm_skip.
        apply perm_swap.
      * apply perm_trans with (0%Z :: 3%Z :: 7%Z :: 12%Z :: 100000%Z :: nil).
        -- apply perm_skip. apply perm_skip. apply perm_skip.
           apply perm_swap.
        -- apply perm_trans with (0%Z :: 3%Z :: 12%Z :: 7%Z :: 100000%Z :: nil).
           ++ apply perm_skip. apply perm_skip.
              apply perm_swap.
           ++ apply Permutation_refl.
  - (* Sorted proof *)
    intros i j Hij x y Hx Hy.
    unfold le_by_cmp, cmp, count_ones, count_ones_pos.
    destruct i as [|i'].
    + (* i = 0 *)
      simpl in Hx. injection Hx as Hx. subst x.
      destruct j as [|j']; [lia|].
      destruct j' as [|j''].
      * simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
      * destruct j'' as [|j'''].
        -- simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
        -- destruct j''' as [|j''''].
           ++ simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
           ++ destruct j'''' as [|j'''''].
              ** simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
              ** simpl in Hy. destruct j'''''; discriminate.
    + (* i > 0 *)
      destruct i' as [|i''].
      * (* i = 1 *)
        simpl in Hx. injection Hx as Hx. subst x.
        destruct j as [|j']; [lia|].
        destruct j' as [|j'']; [lia|].
        destruct j'' as [|j'''].
        -- simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
        -- destruct j''' as [|j''''].
           ++ simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
           ++ destruct j'''' as [|j'''''].
              ** simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
              ** simpl in Hy. destruct j'''''; discriminate.
      * (* i = 2 *)
        destruct i'' as [|i'''].
        -- simpl in Hx. injection Hx as Hx. subst x.
           destruct j as [|j']; [lia|].
           destruct j' as [|j'']; [lia|].
           destruct j'' as [|j''']; [lia|].
           destruct j''' as [|j''''].
           ++ simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
           ++ destruct j'''' as [|j'''''].
              ** simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
              ** simpl in Hy. destruct j'''''; discriminate.
        -- (* i = 3 *)
           destruct i''' as [|i''''].
           ++ simpl in Hx. injection Hx as Hx. subst x.
              destruct j as [|j']; [lia|].
              destruct j' as [|j'']; [lia|].
              destruct j'' as [|j''']; [lia|].
              destruct j''' as [|j'''']; [lia|].
              destruct j'''' as [|j'''''].
              ** simpl in Hy. injection Hy as Hy. subst y. simpl. trivial.
              ** simpl in Hy. destruct j'''''; discriminate.
           ++ (* i >= 4 *)
              destruct i'''' as [|i'''''].
              ** simpl in Hx. injection Hx as Hx. subst x.
                 destruct j as [|j']; [lia|].
                 destruct j' as [|j'']; [lia|].
                 destruct j'' as [|j''']; [lia|].
                 destruct j''' as [|j'''']; [lia|].
                 destruct j'''' as [|j''''']; [lia|].
                 simpl in Hy. destruct j'''''; discriminate.
              ** simpl in Hx. destruct i'''''; discriminate.
Qed.