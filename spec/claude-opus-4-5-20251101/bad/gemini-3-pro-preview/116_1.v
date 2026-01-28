Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

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

Example test_sort_example: sort_array_spec [1; 5; 2; 3; 4] [1; 2; 4; 3; 5].
Proof.
  split.
  - (* Permutation proof *)
    (* Goal: Permutation [1; 5; 2; 3; 4] [1; 2; 4; 3; 5] *)
    apply perm_skip. (* Match 1 *)
    (* Goal: Permutation [5; 2; 3; 4] [2; 4; 3; 5] *)
    transitivity (2 :: 5 :: 3 :: 4 :: nil).
    { apply perm_swap. } (* Swap 5 and 2 *)
    apply perm_skip. (* Match 2 *)
    (* Goal: Permutation [5; 3; 4] [4; 3; 5] *)
    transitivity (3 :: 5 :: 4 :: nil).
    { apply perm_swap. } (* Swap 5 and 3 *)
    transitivity (3 :: 4 :: 5 :: nil).
    { apply perm_skip. apply perm_swap. } (* Swap 5 and 4 *)
    apply perm_swap. (* Swap 3 and 4 to match [4; 3; 5] *)
  - (* Sortedness proof *)
    intros i j Hlt x y Hx Hy.
    (* We iterate through all indices for i *)
    destruct i as [|i].
    + (* i = 0 *)
      simpl in Hx. injection Hx as ->.
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
      destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
      destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
      destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
      simpl in Hy; discriminate.
    + destruct i as [|i].
      * (* i = 1 *)
        simpl in Hx. injection Hx as ->.
        destruct j as [|j]; [lia| destruct j as [|j]; [lia|]].
        destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
        destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
        destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
        simpl in Hy; discriminate.
      * destruct i as [|i].
        -- (* i = 2 *)
           simpl in Hx. injection Hx as ->.
           destruct j as [|j]; [lia| destruct j as [|j]; [lia| destruct j as [|j]; [lia|]]].
           destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
           destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
           simpl in Hy; discriminate.
        -- destruct i as [|i].
           ++ (* i = 3 *)
              simpl in Hx. injection Hx as ->.
              destruct j as [|j]; [lia| destruct j as [|j]; [lia| destruct j as [|j]; [lia| destruct j as [|j]; [lia|]]]].
              destruct j as [|j]; [simpl in Hy; injection Hy as ->; vm_compute; exact I|].
              simpl in Hy; discriminate.
           ++ (* i >= 4 *)
              simpl in Hx.
              destruct i as [|i].
              ** (* i = 4 *)
                 simpl in Hx. injection Hx as ->.
                 (* j must be > 4 for Hlt to hold, but list length is 5 *)
                 destruct j as [|j]; [lia| destruct j as [|j]; [lia| destruct j as [|j]; [lia| destruct j as [|j]; [lia| destruct j as [|j]; [lia|]]]]].
                 simpl in Hy. discriminate.
              ** simpl in Hx. discriminate.
Qed.