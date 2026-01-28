Require Import Coq.Lists.List Coq.Arith.Arith Coq.micromega.Lia.
Import ListNotations.

Definition Grid := list (list nat).
Definition Pos := (nat * nat)%type.

Inductive in_bounds_rel : Grid -> Pos -> Prop :=
| ibr_build : forall grid p r c, p = (r, c) ->
   r < length grid ->
   (exists row, nth_error grid r = Some row /\ c < length row) ->
   in_bounds_rel grid p.

Inductive neighbor_rel : Pos -> Pos -> Prop :=
| nr_right : forall r c, neighbor_rel (r, c) (r, S c)
| nr_down : forall r c, neighbor_rel (r, c) (S r, c)
| nr_left : forall r c, 0 < c -> neighbor_rel (r, c) (r, c - 1)
| nr_up : forall r c, 0 < r -> neighbor_rel (r, c) (r - 1, c).

Definition get_val_rel (grid : Grid) (p : Pos) : nat :=
  let '(r, c) := p in
  match nth_error grid r with
  | Some row => match nth_error row c with Some v => v | None => 0 end
  | None => 0
  end.

Inductive path_in_grid_rel : Grid -> list Pos -> Prop :=
| pigr_single : forall grid p, in_bounds_rel grid p -> path_in_grid_rel grid (p :: nil)
| pigr_step : forall grid p ps q, path_in_grid_rel grid (p :: ps) ->
   neighbor_rel p q -> in_bounds_rel grid q ->
   path_in_grid_rel grid (q :: p :: ps).

Inductive path_values_rel : Grid -> list Pos -> list nat -> Prop :=
| pvr_def : forall grid path,
   path_values_rel grid path (map (get_val_rel grid) (rev path)).

Inductive lex_le_rel : list nat -> list nat -> Prop :=
| llr_nil : forall l2, lex_le_rel nil l2
| llr_lt : forall h1 t1 h2 t2, h1 < h2 -> lex_le_rel (h1 :: t1) (h2 :: t2)
| llr_eq : forall h t1 t2, lex_le_rel t1 t2 -> lex_le_rel (h :: t1) (h :: t2).

Inductive min_path_values_rel : Grid -> nat -> list nat -> Prop :=
| mpvr_build : forall grid k values path,
    path_in_grid_rel grid path -> length path = k ->
    path_values_rel grid path values ->
    (forall path' values', path_in_grid_rel grid path' -> length path' = k ->
        path_values_rel grid path' values' -> lex_le_rel values values') ->
    min_path_values_rel grid k values.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.
  
Definition find_minimum_path_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  min_path_values_rel grid k output.

(* Test Case *)
Definition my_grid : Grid := [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]].
Definition my_k : nat := 3.
Definition my_output : list nat := [1; 2; 1].

(* Helper Tactics *)
Ltac solve_bounds :=
  econstructor; [reflexivity | simpl; lia | simpl; eexists; split; [reflexivity | simpl; lia]].

Example test_example : find_minimum_path_spec my_grid my_k my_output.
Proof.
  unfold find_minimum_path_spec, my_grid, my_k, my_output.
  (* The path is (0,0) -> (0,1) -> (0,0). In reverse list form: [(0,0); (0,1); (0,0)] *)
  eapply mpvr_build with (path := [(0,0); (0,1); (0,0)]).
  
  - (* path_in_grid_rel *)
    apply pigr_step.
    + apply pigr_step.
      * apply pigr_single. solve_bounds.
      * apply nr_right.
      * solve_bounds.
    + apply nr_left. lia.
    + solve_bounds.
    
  - (* length *)
    reflexivity.
    
  - (* path_values_rel *)
    constructor. simpl. reflexivity.
    
  - (* Minimality *)
    intros path' values' Hpath Hlen Hvals.
    (* path' must be length 3 *)
    destruct path' as [|p3 [|p2 [|p1 [|]]]]; simpl in Hlen; try lia.
    
    (* Invert path structure to expose neighbors *)
    inversion Hpath as [|? ? ? ? Hstep3 Hneigh3 Hin3]; subst.
    inversion Hstep3 as [|? ? ? ? Hstep2 Hneigh2 Hin2]; subst.
    inversion Hstep2 as [? ? Hin1]; subst.
    
    inversion Hvals; subst. simpl.
    
    (* Analyze p1 (start) *)
    destruct p1 as [r1 c1].
    inversion Hin1 as [? ? ? ? Heq Hr Hc]; subst; clear Hin1.
    simpl in Hr.
    
    (* Case analysis on start position (r1, c1) *)
    (* Grid is 3x3, so r1, c1 in {0,1,2} *)
    destruct r1 as [|r1]; [|destruct r1 as [|r1]; [|destruct r1 as [|r1]; [|lia]]].
    all: destruct c1 as [|c1]; [|destruct c1 as [|c1]; [|destruct c1 as [|c1]; [|lia]]].
    
    (* Now we have 9 subgoals. 
       Goal 1 is (0,0). 
       Goals 2-9 are other cells, all with value > 1. *)
    
    (* Handle (0,0) *)
    1: {
      apply llr_eq.
      (* p1 = (0,0). Analyze p2. *)
      inversion Hneigh2; subst.
      + (* nr_right: p2 = (0,1). Val 2. Matches output. *)
        apply llr_eq.
        (* p2 = (0,1). Analyze p3. *)
        inversion Hneigh3; subst.
        * (* nr_right: p3 = (0,2). Val 3 > 1 *)
          apply llr_lt. simpl. lia.
        * (* nr_down: p3 = (1,1). Val 5 > 1 *)
          apply llr_lt. simpl. lia.
        * (* nr_left: p3 = (0,0). Val 1 = 1 *)
          apply llr_eq. apply llr_nil.
        * (* nr_up: impossible *)
          simpl in H. lia.
      + (* nr_down: p2 = (1,0). Val 4 > 2 *)
        apply llr_lt. simpl. lia.
      + (* nr_left: impossible *)
        simpl in H. lia.
      + (* nr_up: impossible *)
        simpl in H. lia.
    }
    
    (* Handle remaining 8 cases where start value > 1 *)
    all: apply llr_lt; simpl; lia.

Qed.